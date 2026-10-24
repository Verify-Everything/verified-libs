#!/usr/bin/env bash
# Mutation check: plant known bugs in a copy of the upstream file and confirm a harness
# fails for each (CBMC exit 10). Exit 0 = every mutant was caught. A STALE line means the sed pattern no
# longer matches upstream (the file changed: update the mutant and re-check the harnesses).
#   bash mutants.sh <upstream.c>
# Edit MUTANTS ("sed-expression::description") and CHECKS ("harness.c len") for your library.
set -u
SRC=$1; HERE=$(cd "$(dirname "$0")" && pwd); TMP=$(mktemp -d); missed=0
MUTANTS=(
  's/i + 7 < len/i + 6 < len/::off-by-one in bounds check'
  's/<= 0x7F/< 0x7F/::boundary flipped'
)
CHECKS=("harness.c 7" "harness.c 9")
for m in "${MUTANTS[@]}"; do
  expr=${m%%::*}; name=${m#*::}
  cp "$SRC" "$TMP/$(basename "$SRC")"; sed -i "$expr" "$TMP/$(basename "$SRC")"
  if cmp -s "$SRC" "$TMP/$(basename "$SRC")"; then echo "STALE  $name"; missed=1; continue; fi
  caught=no
  for c in "${CHECKS[@]}"; do
    set -- $c
    bash "$HERE/run_cbmc.sh" "$TMP/$(basename "$SRC")" "$HERE/$1" "$2" >/dev/null 2>&1; rc=$?
    if [ $rc = 10 ]; then caught="yes ($c)"; break; fi
    [ $rc = 0 ] || { echo "ERROR  $name: run_cbmc exit $rc on $c (not a verdict)"; missed=1; caught=error; break; }
  done
  [ "$caught" = error ] || echo "$caught  $name"; [ "$caught" = no ] && missed=1
done
rm -rf "$TMP"; exit $missed
