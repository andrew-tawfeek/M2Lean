#!/usr/bin/env bash
# Reproducible benchmark driver.  Results are raw JSON conforming to
# reproducibility/benchmark.schema.json; see --help for phase/sample controls.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
exec python3 scripts/benchmark.py "$@"
