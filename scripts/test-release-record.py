#!/usr/bin/env python3
"""Dependency-free tests for scripts/release-record.py."""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).resolve().with_name("release-record.py")
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()


def run(command: list[str], cwd: pathlib.Path, *, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, text=True, capture_output=True, check=check)


def write_json(path: pathlib.Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


class ReleaseRecordTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="m2lean-release-record-")
        self.root = pathlib.Path(self.temporary.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        run(["git", "init", "-q", "-b", "main"], self.repo)
        run(["git", "config", "user.name", "Release Record Test"], self.repo)
        run(["git", "config", "user.email", "release-test@example.invalid"], self.repo)

        manifest_dir = self.repo / "reproducibility"
        manifest_dir.mkdir()
        write_json(
            manifest_dir / "manifest.json",
            {
                "manifestVersion": "1.0.0",
                "artifact": {
                    "name": "M2Lean",
                    "repository": "https://github.com/example/M2Lean",
                    "releaseTag": "v0.2.0",
                    "releaseCommit": None,
                    "archive": None,
                    "paperBenchmarkRecord": None,
                },
            },
        )
        (self.repo / "payload.txt").write_text("tagged payload\n", encoding="utf-8")
        run(["git", "add", "."], self.repo)
        run(["git", "commit", "-q", "-m", "release candidate"], self.repo)
        self.commit = run(["git", "rev-parse", "HEAD"], self.repo).stdout.strip()
        run(["git", "tag", "-a", "v0.2.0", "-m", "M2Lean 0.2.0"], self.repo)

        self.benchmark = self.root / "paper-v0.2.0.json"
        write_json(
            self.benchmark,
            {
                "schema_version": "1.0.0",
                "created_utc": "2026-08-03T12:00:00Z",
                "source": {
                    "git_commit": self.commit,
                    "git_dirty": False,
                    "git_status_porcelain": "",
                    "tracked_diff_sha256": EMPTY_SHA256,
                },
                "phases": {"generation": [], "checker": {}, "lean_elaboration": []},
            },
        )
        self.asset = self.root / "M2Lean-v0.2.0.tar.gz"
        self.asset.write_bytes(b"release asset bytes\n")
        self.output = self.root / "m2lean-v0.2.0-release-record.json"

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def invoke(self, *extra: str, output: pathlib.Path | None = None) -> subprocess.CompletedProcess[str]:
        command = [
            sys.executable,
            str(SCRIPT),
            "--tag",
            "v0.2.0",
            "--benchmark",
            str(self.benchmark),
            "--archive-permalink",
            "https://doi.org/10.5281/zenodo.1234567",
            "--archive-doi",
            "10.5281/zenodo.1234567",
            "--output",
            str(output or self.output),
            *extra,
        ]
        return run(command, self.repo, check=False)

    def test_success_binds_tag_benchmark_manifest_and_asset(self) -> None:
        result = self.invoke("--asset", str(self.asset))
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(self.output.read_text(encoding="utf-8"))
        self.assertEqual(record["release"]["commit"], self.commit)
        self.assertNotEqual(record["release"]["tagObject"], self.commit)
        self.assertEqual(record["benchmark"]["recordedCommit"], self.commit)
        self.assertEqual(record["archive"]["doi"], "10.5281/zenodo.1234567")
        manifest_bytes = (self.repo / "reproducibility/manifest.json").read_bytes()
        self.assertEqual(record["staticManifest"]["sha256"], hashlib.sha256(manifest_bytes).hexdigest())
        self.assertEqual(record["benchmark"]["sha256"], hashlib.sha256(self.benchmark.read_bytes()).hexdigest())
        self.assertEqual(record["releaseAssets"][0]["sha256"], hashlib.sha256(self.asset.read_bytes()).hexdigest())

    def test_rejects_dirty_worktree(self) -> None:
        (self.repo / "untracked.txt").write_text("dirty\n", encoding="utf-8")
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("clean Git worktree", result.stderr)
        self.assertFalse(self.output.exists())

    def test_rejects_lightweight_tag(self) -> None:
        run(["git", "tag", "-d", "v0.2.0"], self.repo)
        run(["git", "tag", "v0.2.0"], self.repo)
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("must be an annotated tag", result.stderr)

    def test_rejects_benchmark_for_another_commit(self) -> None:
        benchmark = json.loads(self.benchmark.read_text(encoding="utf-8"))
        benchmark["source"]["git_commit"] = "0" * 40
        write_json(self.benchmark, benchmark)
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does not match tagged commit", result.stderr)

    def test_rejects_head_after_tag(self) -> None:
        (self.repo / "payload.txt").write_text("post-tag change\n", encoding="utf-8")
        run(["git", "add", "payload.txt"], self.repo)
        run(["git", "commit", "-q", "-m", "post-tag commit"], self.repo)
        result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("is not the commit selected by", result.stderr)

    def test_rejects_output_inside_tagged_tree(self) -> None:
        result = self.invoke(output=self.repo / "release-record.json")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("outside the tagged Git worktree", result.stderr)

    def test_rejects_benchmark_inside_tagged_tree(self) -> None:
        inside = self.repo / "paper-v0.2.0.json"
        inside.write_bytes(self.benchmark.read_bytes())
        run(["git", "add", inside.name], self.repo)
        run(["git", "commit", "-q", "-m", "embed benchmark"], self.repo)
        run(["git", "tag", "-f", "-a", "v0.2.0", "-m", "retag fixture"], self.repo)
        result = self.invoke("--benchmark", str(inside))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("benchmark must be outside", result.stderr)


if __name__ == "__main__":
    unittest.main()
