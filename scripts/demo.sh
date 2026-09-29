#!/usr/bin/env bash
# Local, repeatable demonstration. Source files remain in this checkout.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
export M2LEAN_HOME="$ROOT"
export M2LEAN_BUILD_ROOT="${M2LEAN_BUILD_ROOT:-$HOME/m2lean-lean}"
export M2LEAN_CHECK="$M2LEAN_BUILD_ROOT/.lake/build/bin/m2lean-check"

for tool in M2 lake python3 rsync git; do
  command -v "$tool" >/dev/null || { echo "Missing prerequisite: $tool" >&2; exit 1; }
done
echo "=== 1/4 Prepare the pinned Lean build ==="
bash scripts/lean-build.sh m2lean-check M2Lean.Tactic.Macaulay2
mkdir -p build/demo

echo "=== 2/4 Discover and verify a membership certificate ==="
M2 --script examples/demo/membership.m2
"$M2LEAN_CHECK" build/demo/membership.json -o build/demo/accepted-report.json
python3 - <<'PY'
import json
from pathlib import Path

root = Path('build/demo')
doc = json.loads((root / 'membership.json').read_text())
claim = doc['claims'][0]
print('Certificate cofactors:')
print(json.dumps(claim['evidence']['cofactors'], indent=2))
# Zero cofactors are canonical polynomial data, but cannot witness this f.
for cofactor in claim['evidence']['cofactors']:
    cofactor['terms'] = []
(root / 'tampered.json').write_text(json.dumps(doc, indent=2) + '\n')
PY

echo "=== 3/4 Reject deliberately incorrect evidence ==="
status=0
"$M2LEAN_CHECK" build/demo/tampered.json -o build/demo/rejected-report.json || status=$?
if [ "$status" -ne 1 ]; then
  echo "Expected mathematical rejection (exit 1), got exit $status" >&2
  exit 1
fi
cat build/demo/rejected-report.json
echo

echo "=== 4/4 Elaborate a Lean theorem using live Macaulay2 ==="
# Run Lean directly so the tactic executes even when a previous build is cached.
(
  cd "$M2LEAN_BUILD_ROOT"
  lake env lean "$ROOT/lean/M2Lean/Examples/TacticDemo.lean"
)
echo "DEMO PASSED: valid evidence accepted, tampering rejected, Lean example checked."
echo "Certificates and reports: $ROOT/build/demo"
