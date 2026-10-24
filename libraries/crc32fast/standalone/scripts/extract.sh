#!/usr/bin/env bash
# Fetch the pinned crate, run Charon + Aeneas, and refresh lean/Crc32fast/{Types,Funs}.lean.
# Fails if the set of external functions changed (then the hand-written models
# in lean/Crc32fast/*External.lean must be reviewed against the new templates).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"; source "$here/pins.env"
TOOLS="${TOOLS:-$HOME/tools}"; AE="$TOOLS/aeneas-$AENEAS_RELEASE"
work="$here/_build"; mkdir -p "$work"
if [ ! -d "$work/crate/.git" ]; then git clone -q "$CRATE_REPO" "$work/crate"; fi
git -C "$work/crate" fetch -q origin && git -C "$work/crate" checkout -q --detach "$CRATE_REV"
cp "$here/extract/Cargo.lock" "$work/crate/Cargo.lock" 2>/dev/null || true
( cd "$work/crate" && PATH="$AE:$PATH" charon cargo --preset=aeneas --sysroot default \
    --dest-file "$work/crc32fast.llbc" -- --no-default-features --target "$CHARON_TARGET" --locked )
rm -rf "$work/gen" && mkdir -p "$work/gen"
"$AE/aeneas" -backend lean -split-files -dest "$work/gen" "$work/crc32fast.llbc" > "$work/aeneas.log" 2>&1 || { cat "$work/aeneas.log"; exit 1; }
cp "$work/gen/Types.lean" "$work/gen/Funs.lean" "$here/lean/Crc32fast/"
status=0
for t in FunsExternal_Template TypesExternal_Template; do
  if ! diff -q "$here/extract/templates/$t.lean" "$work/gen/$t.lean" >/dev/null; then
    echo "CHANGED: $t.lean differs from the reviewed copy. Review lean/Crc32fast/*External.lean:"
    diff "$here/extract/templates/$t.lean" "$work/gen/$t.lean" || true
    status=1
  fi
done
exit $status
