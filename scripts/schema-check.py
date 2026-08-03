#!/usr/bin/env python3
"""Apply the protocol JSON Schema to every document expected to be valid.

This is only a structural pre-filter.  scripts/run-checks.sh remains the
authoritative semantic and certificate check.
"""

from __future__ import annotations

import json
import pathlib
import sys

try:
    from jsonschema import Draft202012Validator
except ImportError:
    print(
        "schema-check.py requires the 'jsonschema' package "
        "(Debian/Ubuntu: apt install python3-jsonschema)",
        file=sys.stderr,
    )
    raise SystemExit(2)


ROOT = pathlib.Path(__file__).resolve().parent.parent
SCHEMA_PATH = ROOT / "protocol/schema/m2lean-v0.schema.json"


def relative(path: pathlib.Path) -> str:
    return path.relative_to(ROOT).as_posix()


def main() -> int:
    with SCHEMA_PATH.open(encoding="utf-8") as stream:
        schema = json.load(stream)
    Draft202012Validator.check_schema(schema)
    validator = Draft202012Validator(schema)

    documents = sorted((ROOT / "protocol/fixtures/valid").glob("*.json"))
    documents.extend(sorted((ROOT / "examples").glob("**/*.json")))
    failures = 0
    for path in documents:
        try:
            with path.open(encoding="utf-8") as stream:
                document = json.load(stream)
        except (OSError, json.JSONDecodeError) as error:
            print(f"FAIL (JSON syntax): {relative(path)}: {error}", file=sys.stderr)
            failures += 1
            continue
        errors = sorted(validator.iter_errors(document), key=lambda error: list(error.absolute_path))
        if errors:
            failures += 1
            for error in errors:
                location = "/".join(str(part) for part in error.absolute_path) or "<document>"
                print(f"FAIL (schema): {relative(path)}:{location}: {error.message}", file=sys.stderr)
        else:
            print(f"ok (schema prefilter): {relative(path)}")

    if failures:
        print(f"SCHEMA PREFILTER FAILED: {failures} document(s)", file=sys.stderr)
        return 1
    print(f"SCHEMA PREFILTER PASSED: {len(documents)} documents")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
