#!/usr/bin/env python3
"""Regression tests for fail-closed benchmark provenance."""

from __future__ import annotations

import importlib.util
import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from jsonschema import Draft202012Validator


ROOT = pathlib.Path(__file__).resolve().parent.parent


def load_benchmark_module():
    path = ROOT / "scripts/benchmark.py"
    spec = importlib.util.spec_from_file_location("m2lean_benchmark", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class BenchmarkProvenanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.benchmark = load_benchmark_module()
        with (ROOT / "reproducibility/benchmark.schema.json").open(encoding="utf-8") as stream:
            cls.schema = json.load(stream)

    def test_current_checkout_has_an_exact_commit(self) -> None:
        self.require_git_checkout()
        source = self.benchmark.source_state()
        self.assertRegex(source["git_commit"], r"^[0-9a-f]{40}$")
        self.assertIsInstance(source["git_dirty"], bool)
        self.assertRegex(source["tracked_diff_sha256"], r"^[0-9a-f]{64}$")

    def test_git_failure_cannot_masquerade_as_a_clean_tree(self) -> None:
        failure = subprocess.CompletedProcess(
            args=["git"], returncode=128, stdout="", stderr="fatal: provenance unavailable"
        )
        with mock.patch.object(self.benchmark.subprocess, "run", return_value=failure):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "provenance unavailable"):
                self.benchmark.source_state()

    def test_diff_failure_cannot_masquerade_as_an_empty_diff(self) -> None:
        top_level = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=str(ROOT), stderr=""
        )
        revision = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout="1" * 40, stderr=""
        )
        status = subprocess.CompletedProcess(args=["git"], returncode=0, stdout="", stderr="")
        diff_failure = subprocess.CompletedProcess(
            args=["git"], returncode=128, stdout=b"", stderr=b"fatal: diff unavailable"
        )
        with mock.patch.object(
            self.benchmark.subprocess,
            "run",
            side_effect=[top_level, revision, status, diff_failure],
        ):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "diff unavailable"):
                self.benchmark.source_state()

    def test_status_failure_cannot_masquerade_as_a_clean_tree(self) -> None:
        top_level = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=str(ROOT), stderr=""
        )
        revision = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout="1" * 40, stderr=""
        )
        status_failure = subprocess.CompletedProcess(
            args=["git"], returncode=128, stdout="", stderr="fatal: status unavailable"
        )
        with mock.patch.object(
            self.benchmark.subprocess,
            "run",
            side_effect=[top_level, revision, status_failure],
        ):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "status unavailable"):
                self.benchmark.source_state()

    def test_revision_failure_cannot_start_measurement(self) -> None:
        top_level = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=str(ROOT), stderr=""
        )
        revision_failure = subprocess.CompletedProcess(
            args=["git"], returncode=128, stdout="", stderr="fatal: no revision"
        )
        with mock.patch.object(
            self.benchmark.subprocess, "run", side_effect=[top_level, revision_failure]
        ):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "no revision"):
                self.benchmark.source_state()

    def test_missing_git_is_a_controlled_failure(self) -> None:
        with mock.patch.object(self.benchmark.subprocess, "run", side_effect=OSError("git missing")):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "git missing"):
                self.benchmark.source_state()

    def test_provenance_commands_trust_only_the_exact_root(self) -> None:
        commit = "1" * 40

        def completed(argv, **kwargs):
            if kwargs.get("text"):
                if "--show-toplevel" in argv:
                    stdout = str(self.benchmark.ROOT.resolve())
                else:
                    stdout = commit if "rev-parse" in argv else ""
                return subprocess.CompletedProcess(argv, 0, stdout=stdout, stderr="")
            return subprocess.CompletedProcess(argv, 0, stdout=b"", stderr=b"")

        with mock.patch.object(self.benchmark.subprocess, "run", side_effect=completed) as run:
            source = self.benchmark.source_state()
        self.assertEqual(source["git_commit"], commit)
        prefix = ["git", "-c", f"safe.directory={self.benchmark.ROOT.resolve()}"]
        self.assertTrue(run.call_args_list)
        for call in run.call_args_list:
            self.assertEqual(call.args[0][:3], prefix)
            self.assertNotIn("safe.directory=*", call.args[0])

    def test_parent_repository_cannot_supply_provenance(self) -> None:
        parent = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=str(ROOT.parent), stderr=""
        )
        with mock.patch.object(self.benchmark.subprocess, "run", return_value=parent):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "does not match benchmark root"):
                self.benchmark.source_state()

    def test_head_change_during_capture_is_rejected(self) -> None:
        first = "1" * 40
        second = "2" * 40
        top_level = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=str(ROOT), stderr=""
        )
        first_revision = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=first, stderr=""
        )
        status = subprocess.CompletedProcess(args=["git"], returncode=0, stdout="", stderr="")
        diff = subprocess.CompletedProcess(args=["git"], returncode=0, stdout=b"", stderr=b"")
        second_revision = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=second, stderr=""
        )
        with mock.patch.object(
            self.benchmark.subprocess,
            "run",
            side_effect=[top_level, first_revision, status, diff, second_revision],
        ):
            with self.assertRaisesRegex(self.benchmark.BenchmarkError, "HEAD changed"):
                self.benchmark.source_state()

    def require_git_checkout(self) -> None:
        if not (ROOT / ".git").exists():
            self.skipTest("requires Git metadata; source archives intentionally omit .git")

    def checkout_commit(self) -> str:
        self.require_git_checkout()
        return self.benchmark.git_text("rev-parse", "--verify", "HEAD^{commit}")

    def benchmark_document(self, commit: str = "1" * 40) -> dict:
        return {
            "schema_version": "1.0.0",
            "created_utc": "2026-08-04T00:00:00Z",
            "source": {
                "git_commit": commit,
                "git_dirty": False,
                "git_status_porcelain": "",
                "tracked_diff_sha256": hashlib.sha256(b"").hexdigest(),
            },
            "environment": {},
            "configuration": {},
            "phases": {},
        }

    def run_checker(self, document: dict) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="m2lean-benchmark-provenance-") as name:
            path = pathlib.Path(name) / "benchmark.json"
            path.write_text(json.dumps(document), encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(ROOT / "scripts/benchmark-check.py"), "--allow-partial", str(path)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )

    def test_schema_rejects_missing_or_malformed_commits(self) -> None:
        for invalid in (None, "", "1" * 39, "G" * 40, "1" * 41):
            with self.subTest(commit=invalid):
                document = self.benchmark_document()
                document["source"]["git_commit"] = invalid
                errors = list(Draft202012Validator(self.schema).iter_errors(document))
                self.assertTrue(
                    any(list(error.absolute_path) == ["source", "git_commit"] for error in errors)
                )

    def test_checker_accepts_consistent_clean_provenance(self) -> None:
        result = self.run_checker(self.benchmark_document(self.checkout_commit()))
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_checker_rejects_dirty_flag_status_disagreement(self) -> None:
        document = self.benchmark_document(self.checkout_commit())
        document["source"]["git_status_porcelain"] = "?? untracked"
        result = self.run_checker(document)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("dirty flag disagrees", result.stderr)

    def test_checker_rejects_nonempty_diff_for_a_clean_record(self) -> None:
        document = self.benchmark_document(self.checkout_commit())
        document["source"]["tracked_diff_sha256"] = "1" * 64
        result = self.run_checker(document)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("nonempty tracked diff", result.stderr)


if __name__ == "__main__":
    unittest.main()
