#!/usr/bin/env bash
# End-to-end pipeline: run the M2 example scripts, then verify every
# produced document and every protocol fixture with m2lean-check.
# Valid documents must be accepted (exit 0); invalid fixtures must be
# rejected with their declared parse, structural, or verification
# diagnostic class.  Run from the repository root under
# WSL/Linux with M2 on PATH and the Lean exe built
# (scripts/lean-build.sh m2lean-check).
set -uo pipefail
cd "$(dirname "$0")/.."
BIN="${M2LEAN_BUILD_ROOT:-$HOME/m2lean-lean}/.lake/build/bin/m2lean-check"
fail=0

if [ "${SKIP_M2:-0}" != "1" ]; then
  for s in examples/polynomial/polynomial.m2 examples/flagship/flagship.m2 \
           examples/jacobian/jacobian.m2 examples/coloring/coloring.m2 \
           examples/appendix/appendix.m2; do
    echo "--- M2 $s"
    M2 --script "$s" || { echo "M2 FAILED: $s"; fail=1; }
  done
fi

diagnostic_class() {
  case "$(basename "$1")" in
    parse-*) echo parse ;;
    structure-*|noncanonical-*) echo structural ;;
    corrupt-*) echo verification ;;
    *) return 1 ;;
  esac
}

expect() { # expect <accepted|rejected> <file> [diagnostic-class]
  local want="$1" f="$2" class="${3:-}" output code expected_code marker
  output=$("$BIN" "$f" 2>&1)
  code=$?
  if [ "$want" = accepted ] && [ "$code" -ne 0 ]; then
    echo "FAIL: $f should be accepted (exit $code)"
    echo "$output"
    fail=1
  elif [ "$want" = rejected ] && [ "$code" -eq 0 ]; then
    echo "FAIL: $f should be rejected"
    fail=1
  elif [ "$want" = rejected ]; then
    case "$class" in
      parse) expected_code=2; marker='rejected (parse):' ;;
      structural) expected_code=2; marker='rejected (structural):' ;;
      verification) expected_code=1; marker='verification:' ;;
      *)
        echo "FAIL: $f has no expected diagnostic class"
        fail=1
        return
        ;;
    esac
    if [ "$code" -ne "$expected_code" ] || ! grep -Fq "$marker" <<< "$output"; then
      echo "FAIL: $f should be rejected as $class (exit $expected_code)"
      echo "$output"
      fail=1
    else
      echo "ok (rejected/$class): $f"
    fi
  else
    echo "ok ($want): $f"
  fi
}

for f in protocol/fixtures/valid/*.json; do expect accepted "$f"; done
for f in examples/polynomial/polynomial.json examples/flagship/flagship.json \
         examples/jacobian/jacobian.json examples/coloring/*.json \
         examples/appendix/*.json; do
  expect accepted "$f"
done
for f in protocol/fixtures/invalid/*.json; do
  class=$(diagnostic_class "$f") || {
    echo "FAIL: cannot infer diagnostic class for $f"; fail=1; continue;
  }
  expect rejected "$f" "$class"
done

# `deterministic` describes certificate discovery, not verification.
# Check both acceptance and round-trip visibility of the input metadata.
provenance_report=$("$BIN" protocol/fixtures/valid/provenance-nondeterministic.json 2>/dev/null)
if ! grep -Fq '"inputProvenance"' <<< "$provenance_report" ||
   ! grep -Fq '"deterministic": false' <<< "$provenance_report" ||
   ! grep -Fq '"assurance": "proved"' <<< "$provenance_report"; then
  echo "FAIL: nondeterministic input provenance was not retained with checked assurance"
  fail=1
else
  echo "ok (provenance retained/informational)"
fi

if [ "$fail" -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "CHECKS FAILED"; fi
exit "$fail"
