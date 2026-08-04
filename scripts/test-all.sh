#!/usr/bin/env bash
# Complete release/CI test entry point.  It checks the shipped artifacts, then
# deliberately builds only the runtime verifier before regeneration; theorem
# modules are built only after JSON -> Data.lean replay matches the manifest.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "=== 1/8 Verify the shipped generated artifacts ==="
bash scripts/check-generated.sh

echo "=== 2/8 Build the runtime verifier ==="
bash scripts/lean-build.sh m2lean-check

echo "=== 3/8 Regenerate every certificate and Lean literal module ==="
bash scripts/regenerate-all.sh

echo "=== 4/8 Require deterministic generated artifacts ==="
bash scripts/check-generated.sh

echo "=== 5/8 Apply schemas and test release tooling ==="
python3 scripts/schema-check.py
python3 scripts/test-benchmark-provenance.py -q
python3 scripts/test-generated-check.py -q
python3 scripts/test-release-record.py -q

echo "=== 6/8 Verify valid documents and adversarial fixtures ==="
SKIP_M2=1 bash scripts/run-checks.sh

echo "=== 7/8 Build all Lean theorem modules ==="
bash scripts/lean-build.sh
bash scripts/lean-build.sh M2Lean.Examples.TacticDemo

echo "=== 8/8 Audit theorem axioms ==="
bash scripts/audit.sh

echo "ALL REPRODUCIBILITY CHECKS PASSED"
