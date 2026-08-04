#!/usr/bin/env python3
"""Create an external post-tag M2Lean release-identity record.

The output deliberately lives outside the tagged Git tree.  It binds an
annotated tag and exact commit to the static in-tree reproducibility manifest,
a clean benchmark record, an archive permalink/DOI, and optional release
assets without requiring an impossible commit that contains its own hash.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import mimetypes
import os
import pathlib
import re
import subprocess
import sys
from typing import Any
from urllib.parse import urlparse


RECORD_VERSION = "1.0.0"
RECORD_TYPE = "m2lean-post-tag-release"
EMPTY_SHA256 = hashlib.sha256(b"").hexdigest()
FULL_BENCHMARK_PHASES = {"generation", "checker", "lean_elaboration"}
DOI_PATTERN = re.compile(r"^10\.\d{4,9}/\S+$", re.IGNORECASE)


class ReleaseRecordError(RuntimeError):
    pass


def git(repo: pathlib.Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-c", f"safe.directory={repo.resolve()}", *args],
        cwd=repo,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise ReleaseRecordError(f"git {' '.join(args)} failed: {detail}")
    return result.stdout.strip()


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def file_record(path: pathlib.Path, *, name: str | None = None) -> dict[str, Any]:
    media_type, _ = mimetypes.guess_type(path.name)
    return {
        "name": name or path.name,
        "bytes": path.stat().st_size,
        "sha256": sha256_file(path),
        "mediaType": media_type,
    }


def load_json(path: pathlib.Path, label: str) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as stream:
            value = json.load(stream)
    except (OSError, json.JSONDecodeError) as error:
        raise ReleaseRecordError(f"cannot read {label} {path}: {error}") from error
    if not isinstance(value, dict):
        raise ReleaseRecordError(f"{label} must be a JSON object: {path}")
    return value


def normalize_doi(value: str | None) -> str | None:
    if value is None:
        return None
    doi = value.strip()
    for prefix in ("https://doi.org/", "http://doi.org/", "doi:"):
        if doi.lower().startswith(prefix):
            doi = doi[len(prefix):]
            break
    if not DOI_PATTERN.fullmatch(doi):
        raise ReleaseRecordError(f"invalid DOI: {value}")
    return doi


def validate_permalink(value: str) -> str:
    parsed = urlparse(value)
    if parsed.scheme != "https" or not parsed.netloc:
        raise ReleaseRecordError("archive permalink must be an absolute HTTPS URL")
    return value


def is_within(path: pathlib.Path, directory: pathlib.Path) -> bool:
    try:
        return os.path.commonpath((path, directory)) == str(directory)
    except ValueError:
        return False


def validate_static_manifest(manifest: dict[str, Any], tag: str) -> str:
    artifact = manifest.get("artifact")
    if not isinstance(artifact, dict):
        raise ReleaseRecordError("static manifest has no artifact object")
    if artifact.get("releaseTag") != tag:
        raise ReleaseRecordError(
            f"static manifest releaseTag {artifact.get('releaseTag')!r} does not match {tag!r}"
        )
    for field in ("releaseCommit", "archive", "paperBenchmarkRecord"):
        if artifact.get(field) is not None:
            raise ReleaseRecordError(
                f"static manifest field artifact.{field} must remain null; post-tag identity is external"
            )
    repository = artifact.get("repository")
    if not isinstance(repository, str) or not repository.startswith("https://"):
        raise ReleaseRecordError("static manifest artifact.repository must be an HTTPS URL")
    return repository


def validate_benchmark(benchmark: dict[str, Any], commit: str) -> None:
    if "error" in benchmark:
        raise ReleaseRecordError(f"benchmark record contains an error: {benchmark['error']}")
    if benchmark.get("schema_version") != "1.0.0":
        raise ReleaseRecordError("benchmark record must use schema_version 1.0.0")
    if not isinstance(benchmark.get("created_utc"), str):
        raise ReleaseRecordError("benchmark record has no created_utc timestamp")
    source = benchmark.get("source")
    if not isinstance(source, dict):
        raise ReleaseRecordError("benchmark record has no source object")
    if source.get("git_commit") != commit:
        raise ReleaseRecordError(
            f"benchmark commit {source.get('git_commit')!r} does not match tagged commit {commit}"
        )
    if source.get("git_dirty") is not False:
        raise ReleaseRecordError("benchmark was not recorded from a clean Git tree")
    if source.get("git_status_porcelain") != "":
        raise ReleaseRecordError("benchmark records a nonempty Git status")
    if source.get("tracked_diff_sha256") != EMPTY_SHA256:
        raise ReleaseRecordError("benchmark records a nonempty tracked diff")
    phases = benchmark.get("phases")
    if not isinstance(phases, dict) or set(phases) != FULL_BENCHMARK_PHASES:
        raise ReleaseRecordError(
            f"benchmark must contain exactly the full phases {sorted(FULL_BENCHMARK_PHASES)}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True, help="annotated immutable release tag, e.g. v0.2.0")
    parser.add_argument("--benchmark", required=True, type=pathlib.Path, help="clean raw benchmark JSON")
    parser.add_argument("--archive-permalink", required=True, help="permanent HTTPS archive URL")
    parser.add_argument("--archive-doi", help="optional DOI, bare or https://doi.org/... form")
    parser.add_argument(
        "--asset",
        action="append",
        default=[],
        type=pathlib.Path,
        help="optional release asset to hash; may be repeated",
    )
    parser.add_argument(
        "--output",
        required=True,
        type=pathlib.Path,
        help="new record path outside the Git worktree",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        repo = pathlib.Path(git(pathlib.Path.cwd(), "rev-parse", "--show-toplevel")).resolve()
        status = git(repo, "status", "--porcelain=v1", "--untracked-files=all")
        if status:
            raise ReleaseRecordError("release record requires a clean Git worktree")

        output = args.output.expanduser().resolve()
        if is_within(output, repo):
            raise ReleaseRecordError("output must be outside the tagged Git worktree")
        if output.exists():
            raise ReleaseRecordError(f"refusing to overwrite existing output: {output}")
        if not output.parent.is_dir():
            raise ReleaseRecordError(f"output parent directory does not exist: {output.parent}")

        tag_ref = f"refs/tags/{args.tag}"
        tag_type = git(repo, "cat-file", "-t", tag_ref)
        if tag_type != "tag":
            raise ReleaseRecordError(f"{args.tag} must be an annotated tag, not {tag_type!r}")
        tag_object = git(repo, "rev-parse", tag_ref)
        tagged_commit = git(repo, "rev-parse", f"{tag_ref}^{{commit}}")
        head_commit = git(repo, "rev-parse", "HEAD^{commit}")
        if tagged_commit != head_commit:
            raise ReleaseRecordError(
                f"HEAD {head_commit} is not the commit selected by {args.tag} ({tagged_commit})"
            )

        manifest_path = repo / "reproducibility" / "manifest.json"
        manifest = load_json(manifest_path, "static manifest")
        repository = validate_static_manifest(manifest, args.tag)

        benchmark_path = args.benchmark.expanduser().resolve()
        if not benchmark_path.is_file():
            raise ReleaseRecordError(f"benchmark file does not exist: {benchmark_path}")
        if is_within(benchmark_path, repo):
            raise ReleaseRecordError("benchmark must be outside the tagged Git worktree")
        benchmark = load_json(benchmark_path, "benchmark")
        validate_benchmark(benchmark, head_commit)

        assets = []
        asset_names: set[str] = set()
        for raw_path in args.asset:
            path = raw_path.expanduser().resolve()
            if not path.is_file():
                raise ReleaseRecordError(f"release asset does not exist: {path}")
            if path.name in asset_names or path.name == benchmark_path.name:
                raise ReleaseRecordError(f"duplicate release asset name: {path.name}")
            asset_names.add(path.name)
            assets.append(file_record(path))
        assets.sort(key=lambda item: item["name"])

        record = {
            "recordVersion": RECORD_VERSION,
            "recordType": RECORD_TYPE,
            "generatedAt": dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z"),
            "repository": repository,
            "release": {
                "tag": args.tag,
                "tagObject": tag_object,
                "commit": head_commit,
                "tree": git(repo, "rev-parse", "HEAD^{tree}"),
                "commitDate": git(repo, "show", "-s", "--format=%cI", "HEAD"),
            },
            "staticManifest": {
                "path": "reproducibility/manifest.json",
                "bytes": manifest_path.stat().st_size,
                "sha256": sha256_file(manifest_path),
            },
            "benchmark": {
                **file_record(benchmark_path),
                "recordedCommit": benchmark["source"]["git_commit"],
                "createdAt": benchmark.get("created_utc"),
                "phases": sorted(benchmark["phases"]),
            },
            "archive": {
                "permalink": validate_permalink(args.archive_permalink),
                "doi": normalize_doi(args.archive_doi),
            },
            "releaseAssets": assets,
        }

        with output.open("x", encoding="utf-8", newline="\n") as stream:
            json.dump(record, stream, indent=2, ensure_ascii=False)
            stream.write("\n")
        print(f"wrote external post-tag release record: {output}")
        return 0
    except (ReleaseRecordError, OSError) as error:
        print(f"release-record: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
