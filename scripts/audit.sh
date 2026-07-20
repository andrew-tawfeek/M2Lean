#!/usr/bin/env bash
# Axiom audit: the flagship theorems and every soundness theorem must
# depend on at most Lean's three standard axioms.  Fails if sorryAx or
# any unexpected axiom shows up.
set -euo pipefail
cd "$HOME/m2lean-lean"
export PATH="$HOME/.elan/bin:$PATH"
out=$(lake env lean M2Lean/Examples/Audit.lean 2>&1)
echo "$out"
if echo "$out" | grep -qv "depends on axioms: \[propext, Classical.choice, Quot.sound\]"; then
  echo "AUDIT FAILED: unexpected axioms or errors above"
  exit 1
fi
echo "AUDIT PASSED: only propext, Classical.choice, Quot.sound"
