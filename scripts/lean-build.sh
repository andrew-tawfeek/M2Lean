#!/usr/bin/env bash
# Sync the repo's lean/ package into the WSL-native build tree and run
# `lake build` there.  Building on /mnt/c is prohibitively slow, so the
# sources of record live in the repository and builds happen in
# $HOME/m2lean-lean (which keeps its .lake cache between runs).
set -euo pipefail
SRC="$(cd "$(dirname "$0")/.." && pwd)/lean"
DST="$HOME/m2lean-lean"
mkdir -p "$DST"
rsync -a --delete --exclude '.lake' --exclude 'lake-manifest.json' "$SRC/" "$DST/"
cd "$DST"
# a fresh build tree (e.g. CI) needs the pinned manifest and the mathlib cache
if [ ! -f lake-manifest.json ] && [ -f "$SRC/lake-manifest.json" ]; then
  cp "$SRC/lake-manifest.json" .
fi
export PATH="$HOME/.elan/bin:$PATH"
export M2LEAN_HOME="$(cd "$SRC/.." && pwd)"
if [ "${CI:-}" = "true" ] && [ ! -d .lake/packages/mathlib/.lake/build/lib ]; then
  lake exe cache get
fi
lake build "$@"
