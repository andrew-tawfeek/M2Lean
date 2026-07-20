#!/usr/bin/env bash
set -euo pipefail
cd "$HOME/m2lean-lean"
export PATH="$HOME/.elan/bin:$PATH"
for f in M2Lean/Examples/Flagship.lean M2Lean/Examples/Galois.lean; do
  t0=$(date +%s%N)
  lake env lean "$f" > /dev/null 2>&1
  t1=$(date +%s%N)
  ms=$(( (t1-t0)/1000000 ))
  echo "$f elab_ms=$ms"
done
