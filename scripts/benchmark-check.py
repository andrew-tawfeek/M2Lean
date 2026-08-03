#!/usr/bin/env python3
"""Validate a raw benchmark file and its links to the current checkout."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

try:
    from jsonschema import Draft202012Validator
except ImportError:
    print(
        "benchmark-check.py requires the 'jsonschema' package "
        "(Debian/Ubuntu: apt install python3-jsonschema)",
        file=sys.stderr,
    )
    raise SystemExit(2)


ROOT = pathlib.Path(__file__).resolve().parent.parent
SCHEMA_PATH = ROOT / "reproducibility/benchmark.schema.json"


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result", type=pathlib.Path)
    parser.add_argument("--allow-dirty", action="store_true", help="allow a run recorded from a dirty tree")
    parser.add_argument("--allow-partial", action="store_true", help="allow phase-specific smoke output")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    result_path = args.result if args.result.is_absolute() else ROOT / args.result
    with SCHEMA_PATH.open(encoding="utf-8") as stream:
        schema = json.load(stream)
    with result_path.open(encoding="utf-8") as stream:
        result = json.load(stream)

    Draft202012Validator.check_schema(schema)
    errors = sorted(
        Draft202012Validator(schema).iter_errors(result),
        key=lambda error: list(error.absolute_path),
    )
    for error in errors:
        location = "/".join(str(part) for part in error.absolute_path) or "<document>"
        print(f"schema error at {location}: {error.message}", file=sys.stderr)
    if errors:
        return 1
    if "error" in result:
        print(f"benchmark recorded an error: {result['error']}", file=sys.stderr)
        return 1
    if result["source"]["git_dirty"] and not args.allow_dirty:
        print("benchmark was recorded from a dirty Git tree", file=sys.stderr)
        return 1

    phases = result["phases"]
    required_phases = {"generation", "checker", "lean_elaboration"}
    if not args.allow_partial and set(phases) != required_phases:
        print(f"expected phases {sorted(required_phases)}, got {sorted(phases)}", file=sys.stderr)
        return 1

    current_commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    ).stdout.strip()
    if result["source"]["git_commit"] != current_commit:
        print(
            f"benchmark commit {result['source']['git_commit']} does not match checkout {current_commit}",
            file=sys.stderr,
        )
        return 1

    artifacts = []
    for case in phases.get("generation", []):
        artifacts.extend(case["outputs"])
    for document in phases.get("checker", {}).get("documents", []):
        artifacts.append(document)
    for artifact in artifacts:
        path = ROOT / artifact["path"]
        if not path.is_file():
            print(f"missing benchmarked artifact: {artifact['path']}", file=sys.stderr)
            return 1
        actual_size = path.stat().st_size
        actual_hash = sha256_file(path)
        if actual_size != artifact["bytes"] or actual_hash != artifact["sha256"]:
            print(
                f"artifact changed since benchmark: {artifact['path']} "
                f"(expected {artifact['bytes']} bytes, {artifact['sha256']}; "
                f"got {actual_size} bytes, {actual_hash})",
                file=sys.stderr,
            )
            return 1

    print(
        f"BENCHMARK CHECK PASSED: {result_path} "
        f"({len(artifacts)} artifact hash records, commit {current_commit})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
