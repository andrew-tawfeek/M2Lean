#!/usr/bin/env bash
# End-to-end pipeline: run the M2 example scripts, then verify every
# produced document and every protocol fixture with m2lean-check.
# Valid documents must be accepted (exit 0); invalid fixtures must be
# rejected (exit 1 or 2).  Run from the repository root under
# WSL/Linux with M2 on PATH and the Lean exe built
# (scripts/lean-build.sh m2lean-check).
set -uo pipefail
cd "$(dirname "$0")/.."
BIN="$HOME/m2lean-lean/.lake/build/bin/m2lean-check"
fail=0

if [ "${SKIP_M2:-0}" != "1" ]; then
  for s in examples/polynomial/polynomial.m2 examples/flagship/flagship.m2 \
           examples/appendix/appendix.m2; do
    echo "--- M2 $s"
    M2 --script "$s" || { echo "M2 FAILED: $s"; fail=1; }
  done
fi

expect() { # expect <accepted|rejected> <file>
  local want="$1" f="$2"
  "$BIN" "$f" > /dev/null 2>&1
  local code=$?
  if [ "$want" = accepted ] && [ "$code" -ne 0 ]; then
    echo "FAIL: $f should be accepted (exit $code)"; fail=1
  elif [ "$want" = rejected ] && [ "$code" -eq 0 ]; then
    echo "FAIL: $f should be rejected"; fail=1
  else
    echo "ok ($want): $f"
  fi
}

for f in protocol/fixtures/valid/*.json; do expect accepted "$f"; done
for f in examples/polynomial/polynomial.json examples/flagship/flagship.json \
         examples/appendix/*.json; do
  expect accepted "$f"
done
for f in protocol/fixtures/invalid/*.json; do expect rejected "$f"; done

if [ "$fail" -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "CHECKS FAILED"; fi
exit "$fail"
