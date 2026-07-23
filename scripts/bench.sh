#!/usr/bin/env bash
# Micro-benchmark for the paper: document sizes, claim counts, M2
# generation time, and m2lean-check wall time per document.
set -euo pipefail
cd "$(dirname "$0")/.."
BIN="$HOME/m2lean-lean/.lake/build/bin/m2lean-check"

echo "== generation (all example scripts) =="
t0=$(date +%s%N)
M2 --script examples/flagship/flagship.m2 > /dev/null
t1=$(date +%s%N)
echo "flagship.m2 generate_ms=$(( (t1-t0)/1000000 ))"
t0=$(date +%s%N)
M2 --script examples/jacobian/jacobian.m2 > /dev/null
t1=$(date +%s%N)
echo "jacobian.m2 generate_ms=$(( (t1-t0)/1000000 ))"
t0=$(date +%s%N)
M2 --script examples/coloring/coloring.m2 > /dev/null
t1=$(date +%s%N)
echo "coloring.m2 (2 docs) generate_ms=$(( (t1-t0)/1000000 ))"
t0=$(date +%s%N)
M2 --script examples/appendix/appendix.m2 > /dev/null
t1=$(date +%s%N)
echo "appendix.m2 (6 docs) generate_ms=$(( (t1-t0)/1000000 ))"

echo "== verification =="
for f in examples/flagship/flagship.json examples/jacobian/jacobian.json \
         examples/coloring/grotzsch.json examples/coloring/wheel5.json \
         examples/appendix/primefield.json \
         examples/appendix/coloring.json examples/polynomial/polynomial.json \
         examples/appendix/galois.json examples/appendix/toric.json \
         examples/appendix/stanley-reisner.json examples/appendix/symmetric.json; do
  sz=$(wc -c < "$f")
  n=$(python3 -c "import json;print(len(json.load(open('$f'))['claims']))")
  # warm run then 3 timed runs, report the median-ish middle
  "$BIN" "$f" > /dev/null 2>&1
  times=()
  for i in 1 2 3; do
    t0=$(date +%s%N)
    "$BIN" "$f" > /dev/null 2>&1
    t1=$(date +%s%N)
    times+=($(( (t1-t0)/1000000 )))
  done
  IFS=$'\n' sorted=($(sort -n <<<"${times[*]}")); unset IFS
  echo "$f claims=$n bytes=$sz check_ms=${sorted[1]}"
done
