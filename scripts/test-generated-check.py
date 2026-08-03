#!/usr/bin/env python3
"""Regression tests for the generated-artifact integrity gate."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest


CHECKER = pathlib.Path(__file__).with_name("check-generated.py")


class GeneratedArtifactCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temporary.name)
        self.files = {
            "examples/demo/demo.json": b'{"demo":true}\n',
            "lean/M2Lean/Examples/DemoData.lean": b"def demo := true\n",
        }
        self.write_release_metadata()

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def digest(self, content: bytes) -> str:
        return hashlib.sha256(content).hexdigest()

    def write_release_metadata(
        self,
        *,
        manifest_entries: list[dict[str, str]] | None = None,
        ledger_lines: list[str] | None = None,
    ) -> None:
        for relative, content in self.files.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        entries = (
            [
                {"path": relative, "sha256": self.digest(content)}
                for relative, content in sorted(self.files.items())
            ]
            if manifest_entries is None
            else manifest_entries
        )
        reproducibility = self.root / "reproducibility"
        reproducibility.mkdir(exist_ok=True)
        (reproducibility / "manifest.json").write_text(
            json.dumps({"generatedArtifacts": entries}), encoding="utf-8"
        )
        lines = (
            [f"{entry['sha256']}  {entry['path']}" for entry in entries]
            if ledger_lines is None
            else ledger_lines
        )
        content = "\n".join(lines) + ("\n" if lines else "")
        (reproducibility / "generated.sha256").write_bytes(content.encode())

    def run_check(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, str(CHECKER), "--root", str(self.root)],
            check=False,
            capture_output=True,
            text=True,
        )

    def assert_rejected(self, phrase: str) -> None:
        result = self.run_check()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(phrase, result.stderr)

    def test_accepts_exact_release_set(self) -> None:
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("2 files match", result.stdout)

    def test_rejects_raw_byte_mismatch(self) -> None:
        (self.root / "examples/demo/demo.json").write_bytes(b'{"demo":false}\n')
        self.assert_rejected("raw SHA-256 mismatch")

    def test_rejects_unlisted_generated_output(self) -> None:
        extra = self.root / "examples/demo/untracked.json"
        extra.write_text("{}\n", encoding="utf-8")
        self.assert_rejected("unlisted: examples/demo/untracked.json")

    def test_rejects_ledger_digest_disagreement(self) -> None:
        ledger = self.root / "reproducibility/generated.sha256"
        content = bytearray(ledger.read_bytes())
        content[0] = ord("0") if content[0] != ord("0") else ord("1")
        ledger.write_bytes(content)
        self.assert_rejected("generated.sha256 differs from manifest")

    def test_rejects_duplicate_manifest_path(self) -> None:
        entry = {
            "path": "examples/demo/demo.json",
            "sha256": self.digest(self.files["examples/demo/demo.json"]),
        }
        self.write_release_metadata(manifest_entries=[entry, entry])
        self.assert_rejected("duplicate manifest path")

    def test_rejects_traversal_path(self) -> None:
        entry = {"path": "../escape.json", "sha256": "0" * 64}
        self.write_release_metadata(manifest_entries=[entry])
        self.assert_rejected("unsafe or noncanonical artifact path")

    def test_rejects_windows_drive_relative_path(self) -> None:
        entry = {"path": "C:relative/file.json", "sha256": "0" * 64}
        self.write_release_metadata(manifest_entries=[entry])
        self.assert_rejected("unsafe or noncanonical artifact path")

    def test_rejects_windows_invalid_components(self) -> None:
        for raw_path in (
            "examples/CON.json",
            "examples/trailing./file.json",
            "examples/bad:name.json",
            "examples/tab\tname.json",
        ):
            with self.subTest(path=raw_path):
                entry = {"path": raw_path, "sha256": "0" * 64}
                self.write_release_metadata(manifest_entries=[entry])
                self.assert_rejected("artifact path is not portable")

    def test_rejects_duplicate_json_object_key(self) -> None:
        manifest = self.root / "reproducibility/manifest.json"
        entries = json.loads(manifest.read_text())["generatedArtifacts"]
        manifest.write_bytes(
            (
                '{"generatedArtifacts":[],"generatedArtifacts":'
                + json.dumps(entries)
                + "}"
            ).encode()
        )
        self.assert_rejected("duplicate JSON object key")

    def test_rejects_crlf_ledger(self) -> None:
        ledger = self.root / "reproducibility/generated.sha256"
        ledger.write_bytes(ledger.read_bytes().replace(b"\n", b"\r\n"))
        self.assert_rejected("must use LF endings")

    def test_rejects_ledger_without_final_lf(self) -> None:
        ledger = self.root / "reproducibility/generated.sha256"
        ledger.write_bytes(ledger.read_bytes().rstrip(b"\n"))
        self.assert_rejected("end with a newline")

    def test_rejects_duplicate_ledger_path(self) -> None:
        ledger = self.root / "reproducibility/generated.sha256"
        first = ledger.read_bytes().splitlines()[0]
        ledger.write_bytes(ledger.read_bytes() + first + b"\n")
        self.assert_rejected("duplicate ledger path")

    def test_rejects_unsorted_ledger(self) -> None:
        ledger = self.root / "reproducibility/generated.sha256"
        lines = ledger.read_bytes().splitlines()
        ledger.write_bytes(b"\n".join(reversed(lines)) + b"\n")
        self.assert_rejected("paths are not sorted")

    def test_rejects_case_conflicting_manifest_paths(self) -> None:
        first = {
            "path": "examples/demo/demo.json",
            "sha256": self.digest(self.files["examples/demo/demo.json"]),
        }
        second = {"path": "examples/Demo/demo.json", "sha256": "0" * 64}
        self.write_release_metadata(manifest_entries=[first, second])
        self.assert_rejected("case-conflicting paths")

    def test_rejects_empty_manifest_inventory(self) -> None:
        self.write_release_metadata(manifest_entries=[])
        self.assert_rejected("must be a nonempty array")

    def test_rejects_empty_ledger(self) -> None:
        self.write_release_metadata(ledger_lines=[])
        self.assert_rejected("generated.sha256 is empty")

    def test_rejects_symlinked_artifact(self) -> None:
        path = self.root / "examples/demo/demo.json"
        target = self.root / "target.json"
        target.write_bytes(path.read_bytes())
        path.unlink()
        try:
            os.symlink(target, path)
        except (OSError, NotImplementedError) as error:
            self.skipTest(f"symlinks unavailable: {error}")
        self.assert_rejected("must not be a symlink")

    def test_rejects_symlinked_manifest(self) -> None:
        path = self.root / "reproducibility/manifest.json"
        target = self.root / "manifest-target.json"
        path.replace(target)
        try:
            os.symlink(target, path)
        except (OSError, NotImplementedError) as error:
            self.skipTest(f"symlinks unavailable: {error}")
        self.assert_rejected("manifest must not be a symlink")

    def test_rejects_symlinked_ledger(self) -> None:
        path = self.root / "reproducibility/generated.sha256"
        target = self.root / "ledger-target.sha256"
        path.replace(target)
        try:
            os.symlink(target, path)
        except (OSError, NotImplementedError) as error:
            self.skipTest(f"symlinks unavailable: {error}")
        self.assert_rejected("SHA-256 ledger must not be a symlink")

    def test_rejects_unlisted_symlink_directory(self) -> None:
        target = self.root / "concealed"
        target.mkdir()
        (target / "extra.json").write_text("{}\n", encoding="utf-8")
        link = self.root / "examples/concealed"
        try:
            os.symlink(target, link, target_is_directory=True)
        except (OSError, NotImplementedError) as error:
            self.skipTest(f"symlinks unavailable: {error}")
        self.assert_rejected("generated-output directory must not be a symlink")

    @unittest.skipUnless(os.name == "nt", "Windows junction test")
    def test_rejects_unlisted_windows_junction(self) -> None:
        target = self.root / "junction-target"
        target.mkdir()
        (target / "extra.json").write_text("{}\n", encoding="utf-8")
        junction = self.root / "examples/junction"
        result = subprocess.run(
            ["cmd", "/c", "mklink", "/J", str(junction), str(target)],
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            self.skipTest(f"junctions unavailable: {result.stderr or result.stdout}")
        try:
            self.assert_rejected("generated-output directory must not be a symlink or junction")
        finally:
            os.rmdir(junction)


if __name__ == "__main__":
    unittest.main()
