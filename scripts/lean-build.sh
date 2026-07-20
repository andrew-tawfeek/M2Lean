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
export PATH="$HOME/.elan/bin:$PATH"
lake build "$@"
