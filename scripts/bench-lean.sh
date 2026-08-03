#!/usr/bin/env bash
# Compatibility entry point for theorem-elaboration measurements only.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
exec python3 scripts/benchmark.py --only lean "$@"
