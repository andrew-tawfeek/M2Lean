#!/usr/bin/env python3
"""Verify the complete generated-artifact set and its raw-byte digests.

The JSON manifest is the authoritative inventory.  The sha256sum-compatible
sidecar must be an exact, sorted view of it.  Files are discovered as well as
listed, so a new untracked generated output cannot silently escape the gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import sys
from collections.abc import Iterable


HASH_RE = re.compile(r"[0-9a-f]{64}")
LEDGER_LINE_RE = re.compile(r"([0-9a-f]{64})  (.+)")
WINDOWS_DRIVE_RE = re.compile(r"[A-Za-z]:")
WINDOWS_RESERVED_RE = re.compile(r"(?i:con|prn|aux|nul|com[1-9]|lpt[1-9])")
WINDOWS_INVALID_CHARACTERS = frozenset('<>:"|?*')


class CheckError(Exception):
    """A reproducibility invariant was violated."""


def safe_path(raw: object) -> pathlib.PurePosixPath:
    if not isinstance(raw, str) or not raw:
        raise CheckError("artifact paths must be nonempty strings")
    if "\\" in raw or "\0" in raw:
        raise CheckError(f"artifact path is not portable POSIX syntax: {raw!r}")
    path = pathlib.PurePosixPath(raw)
    if (
        raw == "."
        or not path.parts
        or path.is_absolute()
        or WINDOWS_DRIVE_RE.match(raw)
        or ".." in path.parts
        or path.as_posix() != raw
    ):
        raise CheckError(f"unsafe or noncanonical artifact path: {raw!r}")
    for component in path.parts:
        basename = component.split(".", 1)[0]
        if (
            any(ord(character) < 32 for character in component)
            or any(character in WINDOWS_INVALID_CHARACTERS for character in component)
            or component.endswith((".", " "))
            or WINDOWS_RESERVED_RE.fullmatch(basename) is not None
        ):
            raise CheckError(f"artifact path is not portable: {raw!r}")
    return path


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"duplicate JSON object key in manifest: {key!r}")
        result[key] = value
    return result


def reject_case_conflicts(paths: Iterable[str], label: str) -> None:
    seen: dict[str, str] = {}
    for path in paths:
        folded = path.casefold()
        previous = seen.get(folded)
        if previous is not None and previous != path:
            raise CheckError(
                f"case-conflicting paths in {label}: {previous!r} and {path!r}"
            )
        seen[folded] = path


def is_link(path: pathlib.Path) -> bool:
    """Return true for POSIX symlinks and Windows directory junctions."""

    return path.is_symlink() or bool(
        getattr(path, "is_junction", lambda: False)()
    )


def load_manifest(path: pathlib.Path) -> dict[str, str]:
    try:
        document = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=unique_object
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CheckError(f"cannot read {path}: {error}") from error
    entries = document.get("generatedArtifacts") if isinstance(document, dict) else None
    if not isinstance(entries, list) or not entries:
        raise CheckError("manifest generatedArtifacts must be a nonempty array")

    artifacts: dict[str, str] = {}
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256"}:
            raise CheckError(
                f"manifest generatedArtifacts[{index}] must contain exactly path and sha256"
            )
        path_string = safe_path(entry["path"]).as_posix()
        digest = entry["sha256"]
        if not isinstance(digest, str) or HASH_RE.fullmatch(digest) is None:
            raise CheckError(f"invalid SHA-256 for {path_string!r}")
        if path_string in artifacts:
            raise CheckError(f"duplicate manifest path: {path_string!r}")
        artifacts[path_string] = digest
    reject_case_conflicts(artifacts, "manifest")
    return artifacts


def load_ledger(path: pathlib.Path) -> dict[str, str]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise CheckError(f"cannot read {path}: {error}") from error
    if b"\r" in raw or (raw and not raw.endswith(b"\n")):
        raise CheckError("generated.sha256 must use LF endings and end with a newline")
    try:
        lines = raw.decode("utf-8").splitlines()
    except UnicodeError as error:
        raise CheckError(f"generated.sha256 is not UTF-8: {error}") from error
    if not lines:
        raise CheckError("generated.sha256 is empty")

    artifacts: dict[str, str] = {}
    order: list[str] = []
    for line_number, line in enumerate(lines, start=1):
        match = LEDGER_LINE_RE.fullmatch(line)
        if match is None:
            raise CheckError(f"malformed generated.sha256 line {line_number}")
        digest, raw_path = match.groups()
        path_string = safe_path(raw_path).as_posix()
        if path_string in artifacts:
            raise CheckError(f"duplicate ledger path: {path_string!r}")
        artifacts[path_string] = digest
        order.append(path_string)
    reject_case_conflicts(artifacts, "generated.sha256")
    if order != sorted(order):
        raise CheckError("generated.sha256 paths are not sorted")
    return artifacts


def discover(root: pathlib.Path) -> set[str]:
    # Recursive globbing need not follow symlinked directories.  Reject them
    # explicitly so a directory cannot conceal unlisted generated outputs.
    for base in (root / "examples", root / "lean/M2Lean/Examples"):
        if is_link(base):
            raise CheckError(
                f"generated-output root must not be a symlink or junction: {base}"
            )
        for current, directories, _files in os.walk(base, followlinks=False):
            for directory in directories:
                candidate = pathlib.Path(current) / directory
                if is_link(candidate):
                    relative = candidate.relative_to(root).as_posix()
                    raise CheckError(
                        "generated-output directory must not be a symlink or "
                        f"junction: {relative}"
                    )
    paths = list((root / "examples").glob("**/*.json"))
    paths.extend((root / "lean/M2Lean/Examples").glob("*Data.lean"))
    discovered = {path.relative_to(root).as_posix() for path in paths}
    reject_case_conflicts(discovered, "discovered artifact set")
    return discovered


def require_regular_file(
    root: pathlib.Path, relative: str, *, role: str = "generated artifact"
) -> pathlib.Path:
    root_resolved = root.resolve(strict=True)
    path = root.joinpath(*pathlib.PurePosixPath(relative).parts)
    cursor = root
    for part in pathlib.PurePosixPath(relative).parts:
        cursor = cursor / part
        if is_link(cursor):
            raise CheckError(
                f"{role} must not be a symlink or junction: {relative}"
            )
    try:
        resolved = path.resolve(strict=True)
        resolved.relative_to(root_resolved)
    except (OSError, ValueError) as error:
        raise CheckError(f"{role} is missing or escapes the root: {relative}") from error
    if not resolved.is_file():
        raise CheckError(f"{role} is not a regular file: {relative}")
    return resolved


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def compare_mappings(
    expected: dict[str, str], actual: dict[str, str], actual_label: str
) -> None:
    if expected == actual:
        return
    missing = sorted(expected.keys() - actual.keys())
    extra = sorted(actual.keys() - expected.keys())
    changed = sorted(
        path for path in expected.keys() & actual.keys() if expected[path] != actual[path]
    )
    details: list[str] = []
    if missing:
        details.append(f"missing paths: {', '.join(missing)}")
    if extra:
        details.append(f"extra paths: {', '.join(extra)}")
    if changed:
        details.append(f"digest mismatches: {', '.join(changed)}")
    raise CheckError(f"{actual_label} differs from manifest ({'; '.join(details)})")


def verify(root: pathlib.Path) -> int:
    root = root.resolve(strict=True)
    manifest_path = require_regular_file(
        root, "reproducibility/manifest.json", role="manifest"
    )
    ledger_path = require_regular_file(
        root, "reproducibility/generated.sha256", role="SHA-256 ledger"
    )
    manifest = load_manifest(manifest_path)
    ledger = load_ledger(ledger_path)
    compare_mappings(manifest, ledger, "generated.sha256")

    discovered = discover(root)
    expected_paths = set(manifest)
    if discovered != expected_paths:
        missing = sorted(expected_paths - discovered)
        extra = sorted(discovered - expected_paths)
        details: list[str] = []
        if missing:
            details.append(f"missing: {', '.join(missing)}")
        if extra:
            details.append(f"unlisted: {', '.join(extra)}")
        raise CheckError(f"discovered artifact set differs from manifest ({'; '.join(details)})")

    for relative, expected_digest in sorted(manifest.items()):
        path = require_regular_file(root, relative)
        actual_digest = sha256(path)
        if actual_digest != expected_digest:
            raise CheckError(
                f"raw SHA-256 mismatch for {relative}: expected {expected_digest}, "
                f"got {actual_digest}"
            )
        print(f"{relative}: OK")
    print(
        f"GENERATED FILE CHECK PASSED: {len(manifest)} files match the in-tree "
        "manifest and SHA-256 ledger"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=pathlib.Path(__file__).resolve().parent.parent,
        help="repository or unpacked source-archive root",
    )
    arguments = parser.parse_args()
    try:
        return verify(arguments.root)
    except (CheckError, OSError) as error:
        print(f"GENERATED FILE CHECK FAILED: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
