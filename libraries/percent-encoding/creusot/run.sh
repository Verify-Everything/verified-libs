#!/usr/bin/env bash
# Gate 1 for percent-encoding: Creusot proofs that the original upstream bodies of the functions
# rewritten by rust/aeneas-friendly.patch behave exactly like the patched bodies (which Lean proves).
#
#   bash creusot/run.sh UPSTREAM_CRATE PATCHED_CRATE [WORK_DIR]
#
# UPSTREAM_CRATE / PATCHED_CRATE: the percent_encoding crate folder of the pinned upstream checkout
# and of the patched copy (vpipe makes both: $VPIPE_WORK/percent-encoding/{src,patched}/percent_encoding).
# Needs cargo-creusot 0.14.0 with its Why3/why3find/solvers (see README.md). Exit 0 only if every
# body matches its source and every proof goal is proved.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
UP="$(cd "$1" && pwd)"; PA="$(cd "$2" && pwd)"
WORK="${3:-${VPIPE_WORK:-$HOME/vpipe-work}/percent-encoding/creusot}"
CAP="${CREUSOT_FILE_TIMEOUT:-600}"   # wall-clock seconds per proof file
STD_SHA256="b019630da7e585ab18eff475d7ea820474c3fc0cd05a57706facf37f67ab2705"   # creusot-std-0.14.0.crate

echo "== 1. proved bodies are the real code"
python3 -I "$HERE/check_verbatim.py" --upstream "$UP" --patched "$PA" \
  "$HERE/encode/src/lib.rs" "$HERE/decode/src/lib.rs" "$HERE/lossy/src/lib.rs"

echo "== 2. creusot-std 0.14.0 + creusot-std-fmt.patch"
rm -rf "$WORK"; mkdir -p "$WORK"
cp -r "$HERE/encode" "$HERE/decode" "$HERE/lossy" "$WORK/"
( cd "$WORK/encode" && cargo fetch -q )
CRATE="$(ls "${CARGO_HOME:-$HOME/.cargo}"/registry/cache/*/creusot-std-0.14.0.crate | head -1)"
echo "$STD_SHA256  $CRATE" | sha256sum -c -
mkdir -p "$WORK/std" && tar -xzf "$CRATE" -C "$WORK/std"
patch -s -p1 -d "$WORK/std/creusot-std-0.14.0" -i "$HERE/creusot-std-fmt.patch"
for c in encode decode lossy; do
  printf '\n[patch.crates-io]\ncreusot-std = { path = "%s" }\n' "$WORK/std/creusot-std-0.14.0" >> "$WORK/$c/Cargo.toml"
done

echo "== 3. translate and prove"
export DUNE_DIR_LOCATIONS="why3find:lib:$HOME/.local/share/creusot/share/why3find"
export WHY3CONFIG="$HOME/.local/share/creusot/creusot_why3.conf"
fail=0
grep -q "^debug-assertions = false" "$WORK/lossy/Cargo.toml" || { echo "lossy: debug-assertions must be off"; exit 1; }
for c in encode decode lossy; do
  ( cd "$WORK/$c" && CARGO_INCREMENTAL=0 cargo creusot --dry-run-why3find >/dev/null ) \
    || { echo "FAIL $c: creusot translation"; fail=1; continue; }
  while read -r f; do
    if out=$(cd "$WORK/$c" && timeout "$CAP" why3find prove -j 4 --no-autodetect-provers -t 10s "$f" 2>&1) \
       && ! grep -q "✘" <<<"$out"; then
      echo "ok   $c/$f"
    else
      echo "FAIL $c/$f"; grep -o "Goal [^:]*: ✘ ([0-9/]*)" <<<"$out" | head -3 | sed 's/^/     /'; fail=1
    fi
  done < <(cd "$WORK/$c" && find verif -name '*.coma' | sort)
done
[ "$fail" = 0 ] && echo "== all Creusot goals proved" || { echo "== Creusot: unproved goals"; exit 1; }
