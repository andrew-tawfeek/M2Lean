#!/usr/bin/env python3
"""Run M2Lean benchmarks and retain every raw sample as structured JSON.

The harness is intentionally dependency-free and targets Linux/WSL, matching
the supported artifact environment.  It measures child processes with wait4,
which provides per-command peak resident memory without parsing human output.
"""

from __future__ import annotations

import argparse
import copy
import datetime as dt
import hashlib
import json
import os
import pathlib
import platform
import shlex
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
from typing import Any, Iterable


ROOT = pathlib.Path(__file__).resolve().parent.parent
SCHEMA_VERSION = "1.0.0"

GENERATION_CASES = (
    ("polynomial", "examples/polynomial/polynomial.m2", ("examples/polynomial/polynomial.json",)),
    ("flagship", "examples/flagship/flagship.m2", ("examples/flagship/flagship.json",)),
    ("jacobian", "examples/jacobian/jacobian.m2", ("examples/jacobian/jacobian.json",)),
    (
        "coloring",
        "examples/coloring/coloring.m2",
        ("examples/coloring/grotzsch.json", "examples/coloring/wheel5.json"),
    ),
    (
        "appendix",
        "examples/appendix/appendix.m2",
        (
            "examples/appendix/primefield.json",
            "examples/appendix/coloring.json",
            "examples/appendix/galois.json",
            "examples/appendix/toric.json",
            "examples/appendix/stanley-reisner.json",
            "examples/appendix/symmetric.json",
        ),
    ),
)

VERIFICATION_DOCUMENTS = (
    "examples/flagship/flagship.json",
    "examples/jacobian/jacobian.json",
    "examples/coloring/grotzsch.json",
    "examples/coloring/wheel5.json",
    "examples/appendix/primefield.json",
    "examples/appendix/coloring.json",
    "examples/polynomial/polynomial.json",
    "examples/appendix/galois.json",
    "examples/appendix/toric.json",
    "examples/appendix/stanley-reisner.json",
    "examples/appendix/symmetric.json",
)

LEAN_CASES = (
    ("flagship", "lean/M2Lean/Examples/Flagship.lean"),
    ("galois", "lean/M2Lean/Examples/Galois.lean"),
    ("jacobian", "lean/M2Lean/Examples/Jacobian.lean"),
    ("coloring", "lean/M2Lean/Examples/Coloring.lean"),
)


class BenchmarkError(RuntimeError):
    pass


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def command_text(argv: Iterable[str]) -> str:
    return shlex.join(str(arg) for arg in argv)


def decode_output(stream: Any) -> str:
    stream.seek(0)
    return stream.read().decode("utf-8", errors="replace")


def run_measured(
    argv: list[str],
    *,
    cwd: pathlib.Path,
    expected_exit: int,
    timeout_seconds: float,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    """Run one sample and return wall time, wait4 RSS, and raw output."""
    if not hasattr(os, "wait4"):
        raise BenchmarkError("benchmark.py requires os.wait4 (run it under Linux/WSL)")

    started = time.perf_counter_ns()
    timed_out = False
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            env=env,
            stdout=stdout,
            stderr=stderr,
            start_new_session=True,
        )
        deadline = time.monotonic() + timeout_seconds
        while True:
            pid, status, usage = os.wait4(process.pid, os.WNOHANG)
            if pid == process.pid:
                break
            if time.monotonic() >= deadline:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                _, status, usage = os.wait4(process.pid, 0)
                break
            time.sleep(0.005)
        process.returncode = os.waitstatus_to_exitcode(status)
        elapsed_ms = round((time.perf_counter_ns() - started) / 1_000_000, 3)
        max_rss = int(usage.ru_maxrss)
        if platform.system() == "Darwin":
            max_rss //= 1024
        result = {
            "wall_ms": elapsed_ms,
            "max_rss_kib": max_rss,
            "exit_code": process.returncode,
            "timed_out": timed_out,
            "stdout": decode_output(stdout),
            "stderr": decode_output(stderr),
        }

    if timed_out:
        raise BenchmarkError(f"timed out after {timeout_seconds}s: {command_text(argv)}")
    if process.returncode != expected_exit:
        raise BenchmarkError(
            f"expected exit {expected_exit}, got {process.returncode}: {command_text(argv)}\n"
            f"stderr: {result['stderr']}"
        )
    return result


def sample_command(
    argv: list[str],
    *,
    cwd: pathlib.Path,
    samples: int,
    warmups: int,
    expected_exit: int,
    timeout_seconds: float,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "command": [str(arg) for arg in argv],
        "cwd": str(cwd),
        "expected_exit": expected_exit,
        "warmups": [],
        "samples": [],
    }
    for _ in range(warmups):
        record["warmups"].append(
            run_measured(
                argv,
                cwd=cwd,
                expected_exit=expected_exit,
                timeout_seconds=timeout_seconds,
                env=env,
            )
        )
    for _ in range(samples):
        record["samples"].append(
            run_measured(
                argv,
                cwd=cwd,
                expected_exit=expected_exit,
                timeout_seconds=timeout_seconds,
                env=env,
            )
        )
    record["summary"] = {
        "median_wall_ms": round(statistics.median(s["wall_ms"] for s in record["samples"]), 3),
        "peak_rss_kib": max(s["max_rss_kib"] for s in record["samples"]),
    }
    return record


def read_os_release() -> dict[str, str]:
    path = pathlib.Path("/etc/os-release")
    if not path.exists():
        return {}
    result: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if "=" in line and not line.startswith("#"):
            key, value = line.split("=", 1)
            result[key] = value.strip().strip('"')
    return result


def cpu_model() -> str | None:
    path = pathlib.Path("/proc/cpuinfo")
    if not path.exists():
        return platform.processor() or None
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.lower().startswith("model name"):
            return line.split(":", 1)[1].strip()
    return platform.processor() or None


def total_memory_kib() -> int | None:
    path = pathlib.Path("/proc/meminfo")
    if not path.exists():
        return None
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("MemTotal:"):
            return int(line.split()[1])
    return None


def capture(argv: list[str], *, cwd: pathlib.Path) -> str | None:
    try:
        result = subprocess.run(argv, cwd=cwd, text=True, capture_output=True, check=True)
    except (OSError, subprocess.CalledProcessError):
        return None
    text = (result.stdout + result.stderr).strip()
    return text or None


def source_state() -> dict[str, Any]:
    status = capture(["git", "status", "--porcelain=v1"], cwd=ROOT)
    diff = subprocess.run(
        ["git", "diff", "--binary", "HEAD", "--"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        check=False,
    ).stdout
    return {
        "git_commit": capture(["git", "rev-parse", "HEAD"], cwd=ROOT),
        "git_dirty": bool(status),
        "git_status_porcelain": status or "",
        "tracked_diff_sha256": sha256_bytes(diff),
    }


def environment_record(m2: str, lake: str, lean_root: pathlib.Path) -> dict[str, Any]:
    uname = platform.uname()
    return {
        "platform": platform.platform(),
        "os_release": read_os_release(),
        "kernel": uname.release,
        "machine": uname.machine,
        "cpu_model": cpu_model(),
        "logical_cpu_count": os.cpu_count(),
        "memory_total_kib": total_memory_kib(),
        "python": sys.version.splitlines()[0],
        "tools": {
            "macaulay2": capture([m2, "--version"], cwd=ROOT),
            "lake": capture([lake, "--version"], cwd=lean_root),
            "lean": capture([lake, "env", "lean", "--version"], cwd=lean_root),
        },
    }


def run_generation(args: argparse.Namespace, m2: str) -> list[dict[str, Any]]:
    cases = []
    for name, script, outputs in GENERATION_CASES:
        print(f"generation: {script}", file=sys.stderr, flush=True)
        record = sample_command(
            [m2, "--script", script],
            cwd=ROOT,
            samples=args.generation_samples,
            warmups=0,
            expected_exit=0,
            timeout_seconds=args.timeout_seconds,
        )
        output_records = []
        for relative in outputs:
            path = ROOT / relative
            if not path.is_file():
                raise BenchmarkError(f"generation did not produce {relative}")
            output_records.append(
                {"path": relative, "bytes": path.stat().st_size, "sha256": sha256_file(path)}
            )
        cases.append({"id": name, "script": script, "outputs": output_records, "measurement": record})
    return cases


def run_checker(args: argparse.Namespace, checker: pathlib.Path) -> dict[str, Any]:
    if not checker.is_file():
        raise BenchmarkError(f"missing checker executable: {checker}; run scripts/lean-build.sh m2lean-check")

    print("checker startup baseline", file=sys.stderr, flush=True)
    startup = sample_command(
        [str(checker)],
        cwd=ROOT,
        samples=args.samples,
        warmups=1,
        expected_exit=3,
        timeout_seconds=args.timeout_seconds,
    )
    documents = []
    with tempfile.TemporaryDirectory(prefix="m2lean-benchmark-") as temp_name:
        temp = pathlib.Path(temp_name)
        for relative in VERIFICATION_DOCUMENTS:
            print(f"checker: {relative}", file=sys.stderr, flush=True)
            source = ROOT / relative
            raw = source.read_bytes()
            document = json.loads(raw)
            baseline_document = copy.deepcopy(document)
            baseline_document["claims"] = []
            baseline_path = temp / pathlib.Path(relative).name
            baseline_path.write_text(
                json.dumps(baseline_document, ensure_ascii=False, separators=(",", ":")) + "\n",
                encoding="utf-8",
            )
            no_claim = sample_command(
                [str(checker), str(baseline_path)],
                cwd=ROOT,
                samples=args.samples,
                warmups=1,
                expected_exit=0,
                timeout_seconds=args.timeout_seconds,
            )
            full = sample_command(
                [str(checker), relative],
                cwd=ROOT,
                samples=args.samples,
                warmups=1,
                expected_exit=0,
                timeout_seconds=args.timeout_seconds,
            )
            total_median = full["summary"]["median_wall_ms"]
            baseline_median = no_claim["summary"]["median_wall_ms"]
            documents.append(
                {
                    "path": relative,
                    "document_id": document.get("documentId"),
                    "claim_count": len(document.get("claims", [])),
                    "bytes": len(raw),
                    "sha256": sha256_bytes(raw),
                    "no_claim_parse_validate_baseline": no_claim,
                    "full_verification": full,
                    "estimated_claim_check_ms": round(max(0.0, total_median - baseline_median), 3),
                }
            )
    return {
        "startup_baseline": startup,
        "documents": documents,
        "phase_note": (
            "The executable exposes no internal timers. The no-claim document retains all objects but removes "
            "claims, so the difference is an estimate; process startup, parsing, validation, and checking are "
            "also reported together in every raw full-verification sample."
        ),
    }


def run_lean(args: argparse.Namespace, lake: str, lean_root: pathlib.Path) -> list[dict[str, Any]]:
    if not lean_root.is_dir():
        raise BenchmarkError(f"missing native Lean build tree: {lean_root}; run scripts/lean-build.sh")
    env = os.environ.copy()
    env["PATH"] = str(pathlib.Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    cases = []
    for name, relative in LEAN_CASES:
        print(f"Lean elaboration: {relative}", file=sys.stderr, flush=True)
        record = sample_command(
            [lake, "env", "lean", relative],
            cwd=lean_root,
            samples=args.samples,
            warmups=1,
            expected_exit=0,
            timeout_seconds=args.timeout_seconds,
            env=env,
        )
        cases.append({"id": name, "source": relative, "measurement": record})
    return cases


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=pathlib.Path,
        help="raw JSON output path (default: reproducibility/benchmarks/benchmark-<UTC>.json)",
    )
    parser.add_argument("--only", choices=("all", "generation", "checker", "lean"), default="all")
    parser.add_argument("--samples", type=int, default=3, help="timed checker/Lean samples (default: 3)")
    parser.add_argument(
        "--generation-samples", type=int, default=1, help="timed runs per M2 generation script (default: 1)"
    )
    parser.add_argument("--timeout-seconds", type=float, default=300.0, help="per-process timeout (default: 300)")
    parser.add_argument(
        "--lean-root",
        type=pathlib.Path,
        default=pathlib.Path(os.environ.get("M2LEAN_BUILD_ROOT", pathlib.Path.home() / "m2lean-lean")),
    )
    args = parser.parse_args()
    if args.samples < 1 or args.generation_samples < 1 or args.timeout_seconds <= 0:
        parser.error("sample counts and timeout must be positive")
    return args


def write_result(path: pathlib.Path, result: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    created = dt.datetime.now(dt.timezone.utc)
    output = args.output
    if output is None:
        stamp = created.strftime("%Y%m%dT%H%M%SZ")
        output = ROOT / "reproducibility" / "benchmarks" / f"benchmark-{stamp}.json"
    elif not output.is_absolute():
        output = ROOT / output

    m2 = shutil.which("M2") or "M2"
    lake = shutil.which("lake") or str(pathlib.Path.home() / ".elan" / "bin" / "lake")
    checker = args.lean_root / ".lake" / "build" / "bin" / "m2lean-check"
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "created_utc": created.isoformat().replace("+00:00", "Z"),
        "source": source_state(),
        "environment": environment_record(m2, lake, args.lean_root),
        "configuration": {
            "only": args.only,
            "samples": args.samples,
            "generation_samples": args.generation_samples,
            "warmups": 1,
            "timeout_seconds": args.timeout_seconds,
            "lean_root": str(args.lean_root),
            "checker": str(checker),
        },
        "phases": {},
    }
    try:
        if args.only in ("all", "generation"):
            result["phases"]["generation"] = run_generation(args, m2)
        if args.only in ("all", "checker"):
            result["phases"]["checker"] = run_checker(args, checker)
        if args.only in ("all", "lean"):
            result["phases"]["lean_elaboration"] = run_lean(args, lake, args.lean_root)
    except (BenchmarkError, OSError, json.JSONDecodeError) as error:
        result["error"] = str(error)
        write_result(output, result)
        print(f"benchmark failed; partial raw results: {output}", file=sys.stderr)
        print(error, file=sys.stderr)
        return 1

    write_result(output, result)
    print(f"raw benchmark results: {output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
