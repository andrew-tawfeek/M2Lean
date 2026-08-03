#!/usr/bin/env bash
# Verify generated artifacts without relying on Git metadata.  This works in a
# checkout, a GitHub source archive, or an unpacked archival deposit.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 "$ROOT/scripts/check-generated.py" --root "$ROOT"
