#!/usr/bin/env bash
# Gate 1 for crc32fast: patches/0002-simd-readable-by-aeneas.patch (made only so Aeneas can read
# the SIMD kernels) does not change behaviour.
#
#   bash equivalence/run.sh UPSTREAM_CRATE [WORK_DIR]
#
# UPSTREAM_CRATE: a checkout of the pinned upstream commit (vpipe makes one). This script builds
# two copies: orig = upstream + patches/0001 (the proved fix), patched = orig + patches/0002.
# Needs cargo-creusot 0.14.0 with its Why3/why3find/solvers (see README.md) and a Rust toolchain
# with the x86_64-unknown-linux-gnu target. Exit 0 only if every check passes.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
LIB="$(cd "$HERE/.." && pwd)"
UP="$(cd "$1" && pwd)"
WORK="${2:-${VPIPE_WORK:-$HOME/vpipe-work}/crc32fast/equivalence}"
CAP="${CREUSOT_FILE_TIMEOUT:-600}"   # wall-clock seconds per proof file
STD_SHA256="b019630da7e585ab18eff475d7ea820474c3fc0cd05a57706facf37f67ab2705"   # creusot-std-0.14.0.crate

echo "== 0. trees: orig = upstream + 0001, patched = orig + 0002"
rm -rf "$WORK"; mkdir -p "$WORK"
for t in orig patched; do
  mkdir "$WORK/$t"
  ( cd "$UP" && git archive HEAD ) | tar -x -C "$WORK/$t"
  patch -s -p1 -d "$WORK/$t" -i "$LIB/patches/0001-hasher-wrapping-add.patch"
done
patch -s -p1 -d "$WORK/patched" -i "$LIB/patches/0002-simd-readable-by-aeneas.patch"
# Everything 0002 changes is covered below: aarch64.rs by Creusot, pclmulqdq.rs by the assembly check.
changed=$( { diff -rq "$WORK/orig" "$WORK/patched" || true; } | awk '{print $2}' | sed "s#^$WORK/orig/##" | sort | tr '\n' ' ')
[ "$changed" = "src/specialized/aarch64.rs src/specialized/pclmulqdq.rs " ] \
  || { echo "unexpected files changed by 0002: $changed"; exit 1; }

echo "== 1. x86: identical assembly (pclmulqdq.rs load helpers)"
bash "$HERE/x86_asm.sh" "$WORK/orig" "$WORK/patched" "$WORK/x86-asm"

echo "== 2. aarch64: proved bodies are the real code"
python3 -I "$HERE/check_verbatim.py" --upstream "$WORK/orig" --patched "$WORK/patched" \
  "$HERE/aarch64/src/lib.rs"

echo "== 3. creusot-std 0.14.0 + creusot-std-chunks.patch"
cp -r "$HERE/aarch64" "$WORK/aarch64"
( cd "$WORK/aarch64" && cargo fetch -q )
CRATE="$(ls "${CARGO_HOME:-$HOME/.cargo}"/registry/cache/*/creusot-std-0.14.0.crate | head -1)"
echo "$STD_SHA256  $CRATE" | sha256sum -c -
mkdir -p "$WORK/std" && tar -xzf "$CRATE" -C "$WORK/std"
patch -s -p1 -d "$WORK/std/creusot-std-0.14.0" -i "$HERE/creusot-std-chunks.patch"
printf '\n[patch.crates-io]\ncreusot-std = { path = "%s" }\n' "$WORK/std/creusot-std-0.14.0" >> "$WORK/aarch64/Cargo.toml"

echo "== 4. aarch64: translate and prove"
export PATH="$HOME/.local/share/creusot/bin:$PATH"
export DUNE_DIR_LOCATIONS="why3find:lib:$HOME/.local/share/creusot/share/why3find"
export WHY3CONFIG="$HOME/.local/share/creusot/creusot_why3.conf"
fail=0
( cd "$WORK/aarch64" && CARGO_INCREMENTAL=0 cargo creusot --dry-run-why3find >/dev/null ) \
  || { echo "FAIL aarch64: creusot translation"; exit 1; }
while read -r f; do
  if out=$(cd "$WORK/aarch64" && timeout "$CAP" why3find prove -j 4 --no-autodetect-provers -t 10s "$f" 2>&1) \
     && ! grep -q "✘" <<<"$out"; then
    echo "ok   $f"
  else
    echo "FAIL $f"; grep -o "Goal [^:]*: ✘ ([0-9/]*)" <<<"$out" | head -3 | sed 's/^/     /'; fail=1
  fi
done < <(cd "$WORK/aarch64" && find verif -name '*.coma' | sort)
[ "$fail" = 0 ] && echo "== all checks passed" || { echo "== Creusot: unproved goals"; exit 1; }
