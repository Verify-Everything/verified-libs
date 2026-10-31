#!/usr/bin/env bash
# Gate 1, x86 half of patches/0002-simd-readable-by-aeneas.patch: the patch only moves the three
# unaligned loads in src/specialized/pclmulqdq.rs into `#[inline]` helpers (load128/256/512).
# Creusot cannot prove that (it does not model `<[u8]>::as_ptr` returning the same address on two
# calls), so this checks that rustc emits identical x86_64 assembly for the crate with and without
# the patch, in every build configuration the crate supports on x86_64.
#
#   bash equivalence/x86_asm.sh ORIG_CRATE PATCHED_CRATE [WORK_DIR]
#
# ORIG_CRATE: pinned upstream + patches/0001 (the proved fix). PATCHED_CRATE: the same + 0002.
# Exit 0 only if all 8 configurations give identical assembly (ignoring .file/.loc/.ident
# lines, which carry source paths and line numbers) and both planted changes are caught.
# This is compiler-checked equality of the release machine code for the rustc it runs, not a
# source-level proof; opt-level=0 builds (helpers not inlined) are not compared.
set -euo pipefail
OR="$(cd "$1" && pwd)"; PA="$(cd "$2" && pwd)"
WORK="${3:-${VPIPE_WORK:-$HOME/vpipe-work}/crc32fast/x86-asm}"
TARGET=x86_64-unknown-linux-gnu
rm -rf "$WORK"; mkdir -p "$WORK"
rustc --version

asm() {  # asm CRATE NAME DEBUG_ASSERTIONS CARGO_FLAGS... -> path of the .s file
  local crate="$1" name="$2" da="$3"; shift 3
  ( cd "$crate" && CARGO_TARGET_DIR="$WORK/$name" RUSTFLAGS="-C debug-assertions=$da" \
      cargo rustc -q --release --lib --target "$TARGET" "$@" -- --emit asm -C codegen-units=1 ) >&2
  ls "$WORK/$name/$TARGET/release/deps/"crc32fast-*.s
}
same() { diff -q <(grep -v '^\s*\.\(file\|loc\|ident\)' "$1") <(grep -v '^\s*\.\(file\|loc\|ident\)' "$2") >/dev/null; }

fail=0
for cfg in "std:" "no_std:--no-default-features" "std+nightly:--features=nightly" \
           "no_std+nightly:--no-default-features --features=nightly"; do
  n="${cfg%%:*}"; flags="${cfg#*:}"
  for da in off on; do
    # shellcheck disable=SC2086
    a=$(asm "$OR" "orig-$n-$da" "$da" $flags); b=$(asm "$PA" "patched-$n-$da" "$da" $flags)
    if same "$a" "$b"; then echo "ok   $n debug-assertions=$da ($(wc -l <"$a") lines identical)"
    else echo "FAIL $n debug-assertions=$da: assembly differs"; fail=1; fi
  done
done

# The check must see the kernels the patch touches.
a=$(ls "$WORK/orig-std-on/$TARGET/release/deps/"crc32fast-*.s)
for f in 9calculate 14calculate_avx2 16calculate_avx512 17reduce_128_to_crc; do
  grep -q "pclmulqdq$f" "$a" || { echo "FAIL kernel pclmulqdq::${f#[0-9]*} missing from the assembly"; fail=1; }
done

# Planted changes in the helpers must change the assembly.
plant() {
  local name="$1" from="$2" to="$3" m="$WORK/mutant"
  rm -rf "$m"; cp -r "$PA" "$m"; rm -rf "$m/target"
  python3 -I - "$m/src/specialized/pclmulqdq.rs" "$from" "$to" <<'PY'
import sys
p, f, t = sys.argv[1:]
s = open(p).read()
assert s.count(f) == 1, "pattern missing"
open(p, "w").write(s.replace(f, t))
PY
  b=$(asm "$m" "mutant-$RANDOM" off)
  if same "$(ls "$WORK/orig-std-off/$TARGET/release/deps/"crc32fast-*.s)" "$b"; then
    echo "FAIL planted change not caught: $name"; fail=1
  else echo "ok   planted change caught: $name"; fi
}
plant "load128 reads one byte later" \
  "arch::_mm_loadu_si128(a.as_ptr() as *const arch::__m128i)" \
  "arch::_mm_loadu_si128(a.as_ptr().add(1) as *const arch::__m128i)"
plant "load512 reads only 32 bytes" \
  "arch::_mm512_loadu_si512(a.as_ptr() as *const _)" \
  "arch::_mm512_castsi256_si512(arch::_mm256_loadu_si256(a.as_ptr() as *const _))"

[ "$fail" = 0 ] && echo "== x86: original and patched assembly identical" || { echo "== x86: FAILED"; exit 1; }
