#!/usr/bin/env bash
# Copy the vpipe engine and library proofs from the workshop pipeline into this repo.
# The repo root IS the engine root (bin/vpipe.py, toolchain/, libraries/<lib>/, results/ ...).
# Toolkit-owned files (README.md, bin/vkit*, skills/, docs/, install.sh, .github/ ...) are kept.
# Once verified-libs is the source of truth this script is no longer needed.
#   bash scripts/sync-engine.sh [/path/to/pipeline] [/path/to/verification-notes]
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
SRC=${1:-/mnt/project-files/pipeline}
NOTES=${2:-/mnt/project-files/verification-notes}
[ -f "$SRC/bin/vpipe.py" ] || { echo "no vpipe at $SRC" >&2; exit 1; }
ENGINE=(VERSION bootstrap.sh bin/vpipe bin/vpipe.py bin/standards.py toolchain templates checklists self selftest libraries candidates results)
# Toolkit-owned files inside engine folders survive the copy.
KEEP=(templates/CLAIM.md)
keep=$(mktemp -d); for k in "${KEEP[@]}"; do [ -e "$HERE/$k" ] && mkdir -p "$keep/$(dirname "$k")" && cp "$HERE/$k" "$keep/$k"; done
for p in "${ENGINE[@]}"; do
  [ -e "$SRC/$p" ] || continue
  rm -rf "${HERE:?}/$p"; mkdir -p "$(dirname "$HERE/$p")"
  ( cd "$SRC" && tar cf - --exclude .lake --exclude target --exclude __pycache__ \
      --exclude 'self/snapshots/*' --exclude 'self/.*.lock' --exclude '*.tar.zst' --exclude '*.tar.gz' "$p" ) \
    | ( cd "$HERE" && tar xf - )
done
( cd "$keep" && tar cf - . ) | ( cd "$HERE" && tar xf - ); rm -rf "${keep:?}"
# Engine README becomes docs/engine.md; the repo README is the toolkit's.
cp "$SRC/README.md" "$HERE/docs/engine.md"
# Lessons: the engine reads notes/ in the repo when the workshop folder is absent.
mkdir -p "$HERE/notes/libraries"
cp "$NOTES/general.md" "$HERE/notes/general.md"
for f in "$NOTES"/*.md; do
  b=$(basename "$f"); case $b in general.md|pipeline-design.md) continue;; esac
  cp "$f" "$HERE/notes/libraries/$b"
done
cp "$NOTES/pipeline-design.md" "$HERE/docs/pipeline-design.md"
mkdir -p "$HERE/cache" "$HERE/self/snapshots"; touch "$HERE/cache/.keep" "$HERE/self/snapshots/.keep"
echo "synced engine $(cat "$HERE/VERSION") from $SRC"
