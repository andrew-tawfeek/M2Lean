#!/usr/bin/env bash
# Sync the root Lake package and its lean/ sources into a WSL-native tree and run
# `lake build` there.  Building on /mnt/c is prohibitively slow, so the
# sources of record live in the repository and builds happen in
# $HOME/m2lean-lean (which may keep its .lake cache between runs).
set -euo pipefail
SRC="$(cd "$(dirname "$0")/.." && pwd)"
DST="${M2LEAN_BUILD_ROOT:-$HOME/m2lean-lean}"

if [ ! -f "$SRC/lake-manifest.json" ]; then
  echo "missing pinned dependency manifest: $SRC/lake-manifest.json" >&2
  exit 1
fi

mkdir -p "$DST/lean"
rsync -a --delete --exclude '.lake' --exclude 'lakefile.olean' "$SRC/lean/" "$DST/lean/"
for file in lakefile.toml lean-toolchain LICENSE README.md; do
  cp "$SRC/$file" "$DST/$file"
done
# The native build tree is a cache, never a source of dependency truth.  Copy
# the checked-in manifest on every invocation so changing lakefile.toml or the
# pinned manifest cannot leave an older manifest active in $DST.
cp "$SRC/lake-manifest.json" "$DST/lake-manifest.json"

cd "$DST"
export PATH="$HOME/.elan/bin:$PATH"
export M2LEAN_HOME="$SRC"

# A restored .lake cache can contain a half-cloned repository or a package at
# the revision from an older manifest.  Lake's resulting "could not resolve
# HEAD" error is otherwise opaque and persistent.  Treat package directories
# as disposable cache entries: retain only clean Git checkouts at the exact
# revisions in the source manifest and let Lake fetch anything else again.
manifest_packages="$(python3 - "$SRC/lake-manifest.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    manifest = json.load(stream)
for package in manifest.get("packages", []):
    if package.get("type") == "git":
        print(f"{package['name']}\t{package['rev']}")
PY
)"
while IFS=$'\t' read -r package_name package_rev; do
  [ -n "$package_name" ] || continue
  case "$package_name" in
    *[!A-Za-z0-9_.-]*)
      echo "unsafe package name in lake-manifest.json: $package_name" >&2
      exit 1
      ;;
  esac
  package_dir="$DST/.lake/packages/$package_name"
  [ -e "$package_dir" ] || continue
  if [ ! -d "$package_dir/.git" ] || \
     ! actual_rev="$(git -C "$package_dir" rev-parse --verify HEAD 2>/dev/null)" || \
     [ "$actual_rev" != "$package_rev" ] || \
     ! git -C "$package_dir" diff --quiet --ignore-submodules --; then
    case "$package_dir" in
      "$DST"/.lake/packages/*)
        echo "discarding stale or corrupt Lake package cache: $package_name" >&2
        rm -rf -- "$package_dir"
        ;;
      *)
        echo "refusing to remove package outside build cache: $package_dir" >&2
        exit 1
        ;;
    esac
  fi
done <<< "$manifest_packages"

if [ "${CI:-}" = "true" ] && [ ! -d .lake/packages/mathlib/.lake/build/lib ]; then
  lake exe cache get
fi
lake build "$@"
