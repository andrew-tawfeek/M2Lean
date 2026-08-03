#!/usr/bin/env bash
# Regenerate every checked-in Macaulay2 protocol document and every Lean data
# module derived from those documents.  Run from any directory under
# WSL/Linux with M2 and Python 3 on PATH.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

command -v M2 >/dev/null 2>&1 || {
  echo "Macaulay2 executable 'M2' was not found on PATH" >&2
  exit 127
}
command -v python3 >/dev/null 2>&1 || {
  echo "Python executable 'python3' was not found on PATH" >&2
  exit 127
}

m2_scripts=(
  examples/polynomial/polynomial.m2
  examples/flagship/flagship.m2
  examples/jacobian/jacobian.m2
  examples/coloring/coloring.m2
  examples/appendix/appendix.m2
)

for script in "${m2_scripts[@]}"; do
  echo "--- regenerate: $script"
  M2 --script "$script"
done

echo "--- regenerate: Lean certificate literals"
python3 scripts/json2lean.py \
  examples/flagship/flagship.json \
  lean/M2Lean/Examples/FlagshipData.lean \
  M2Lean.Flagship
python3 scripts/json2lean.py \
  examples/jacobian/jacobian.json \
  lean/M2Lean/Examples/JacobianData.lean \
  M2Lean.Jacobian
python3 scripts/json2lean.py \
  examples/coloring/wheel5.json \
  lean/M2Lean/Examples/ColoringData.lean \
  M2Lean.Coloring
python3 scripts/json2lean.py \
  examples/appendix/galois.json \
  lean/M2Lean/Examples/GaloisData.lean \
  M2Lean.Galois

expected_json=(
  examples/polynomial/polynomial.json
  examples/flagship/flagship.json
  examples/jacobian/jacobian.json
  examples/coloring/grotzsch.json
  examples/coloring/wheel5.json
  examples/appendix/primefield.json
  examples/appendix/coloring.json
  examples/appendix/galois.json
  examples/appendix/toric.json
  examples/appendix/stanley-reisner.json
  examples/appendix/symmetric.json
)
for document in "${expected_json[@]}"; do
  if [ ! -s "$document" ]; then
    echo "regeneration did not produce a nonempty document: $document" >&2
    exit 1
  fi
done

echo "REGENERATION COMPLETE: ${#expected_json[@]} JSON documents and 4 Lean data modules"
