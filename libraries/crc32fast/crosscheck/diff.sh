#!/bin/bash
# Differential test of the proved (patched) crc32fast tree against a bitwise reference CRC-32
# and against the pristine upstream tree, on every x86_64 kernel (portable, SSE, AVX2, AVX-512)
# and the std runtime-detection build. Usage: diff.sh <patched-tree> [cases] [pristine-tree]
set -euo pipefail
TREE=$(cd "$1" && pwd); CASES=${2:-50000}
HERE=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
# Pristine upstream: vpipe keeps it next to the patched tree; otherwise pass it as $3.
PRISTINE=${3:-$(dirname "$TREE")/src}
[ -f "$PRISTINE/Cargo.toml" ] || { echo "pristine tree not found: $PRISTINE"; exit 1; }
cp -a "$PRISTINE" "$W/pristine"; rm -rf "$W/pristine/.git" "$W/pristine/target"
# Instrumented copy: records which kernel State::new picked (only to confirm path selection).
cp -a "$TREE" "$W/instr"; rm -rf "$W/instr/.git" "$W/instr/target"
python3 - "$W/instr" <<'P'
import sys; d=sys.argv[1]
p=d+'/src/specialized/pclmulqdq.rs'; s=open(p).read()
old="Self::detect().map(|kind| Self { kind })"; assert old in s
s=s.replace(old,"Self::detect().map(|kind| { crate::__KIND.store(match kind { Kind::Sse => 1, #[cfg(stable_vpclmulqdq)] Kind::Avx2 => 2, #[cfg(stable_vpclmulqdq)] Kind::Avx512 => 3 }, core::sync::atomic::Ordering::SeqCst); Self { kind } })")
open(p,'w').write(s)
p=d+'/src/specialized/aarch64.rs'; s=open(p).read()
assert s.count("Some(Self(()))")==2
s=s.replace("Some(Self(()))","{ crate::__KIND.store(4, core::sync::atomic::Ordering::SeqCst); Some(Self(())) }")
open(p,'w').write(s)
p=d+'/src/lib.rs'; s=open(p).read()
s=s.replace("mod baseline;","#[doc(hidden)]\npub static __KIND: core::sync::atomic::AtomicU8 = core::sync::atomic::AtomicU8::new(0);\nmod baseline;",1)
open(p,'w').write(s)
P
(cd "$TREE" && cargo test -q 2>&1 | grep -E "test result|FAILED|panicked" || true)
(cd "$TREE" && cargo test -q 2>&1 >/dev/null) || { echo "cargo test failed"; exit 1; }
B="-C target-feature=+sse2,+sse4.1,+ssse3,+pclmulqdq"
declare -A RF=([portable]="" [sse]="$B" [avx2]="$B,+avx2,+vpclmulqdq" [avx512]="$B,+avx2,+avx512f,+vpclmulqdq" [std]="")
declare -A WANT=([portable]=0 [sse]=1 [avx2]=2 [avx512]=3)
fail=0
for c in portable sse avx2 avx512 std; do
  FE=""; [ $c = std ] && FE="--features std"
  # which kernel runs (skip configs this CPU cannot execute)
  case $c in avx512) grep -qw avx512f /proc/cpuinfo && grep -qw vpclmulqdq /proc/cpuinfo || { echo "== $c skipped (CPU)"; continue; };;
             avx2) grep -qw avx2 /proc/cpuinfo && grep -qw vpclmulqdq /proc/cpuinfo || { echo "== $c skipped (CPU)"; continue; };; esac
  mkdir -p "$W/k-$c/src"; sed "s#SRC#$W/instr#" "$HERE/harness/Cargo.toml.tmpl" > "$W/k-$c/Cargo.toml"
  echo 'fn main(){let mut h=crc32fast::Hasher::new();h.update(&[0u8;4096]);println!("{}",crc32fast::__KIND.load(core::sync::atomic::Ordering::SeqCst));}' > "$W/k-$c/src/main.rs"
  k=$(cd "$W/k-$c" && RUSTFLAGS="${RF[$c]}" cargo run -q --release $FE)
  if [ $c != std ] && [ "$k" != "${WANT[$c]}" ]; then echo "== $c: wrong kernel $k"; fail=1; continue; fi
  for t in patched pristine; do
    S=$TREE; [ $t = pristine ] && S=$W/pristine
    mkdir -p "$W/$t-$c/src"; cp "$HERE/harness/src/main.rs" "$W/$t-$c/src/"
    sed "s#SRC#$S#" "$HERE/harness/Cargo.toml.tmpl" > "$W/$t-$c/Cargo.toml"
    out=$(cd "$W/$t-$c" && RUSTFLAGS="${RF[$c]}" cargo build -q --release $FE && ./target/release/crcdiff "$CASES" 2>&1 || true)
    echo "== $c kernel=$k $t: $(echo "$out" | grep -E '^ok|overflow case|panicked' | tr '\n' ' ')"
    echo "$out" | grep -q "^ok $CASES cases" || fail=1
    if [ $t = patched ]; then echo "$out" | grep -q "overflow case finalize=8cdc1683 8cdc1683" || fail=1; fi
    if [ $t = pristine ]; then echo "$out" | grep -q "attempt to add with overflow" || { echo "   (expected upstream overflow panic not seen)"; fail=1; }; fi
  done
done
# aarch64 (CRC32B/CRC32X kernel incl. the 3-stream path, portable fallback, std detection) under
# qemu user mode, when qemu-aarch64 and an aarch64 linker are installed.
Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64 || true)
if [ -n "$Q" ] && command -v aarch64-linux-gnu-gcc >/dev/null && rustup target list --installed 2>/dev/null | grep -q aarch64-unknown-linux-gnu; then
  export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc
  export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER="$Q -L /usr/aarch64-linux-gnu"
  declare -A AF=([a64-crc]="-C target-feature=+crc" [a64-portable]="-C target-feature=-crc" [a64-std]="")
  declare -A AW=([a64-crc]=4 [a64-portable]=0 [a64-std]=4)
  for c in a64-crc a64-portable a64-std; do
    FE=""; [ $c = a64-std ] && FE="--features std"
    mkdir -p "$W/k-$c/src"; sed "s#SRC#$W/instr#" "$HERE/harness/Cargo.toml.tmpl" > "$W/k-$c/Cargo.toml"
    echo 'fn main(){let mut h=crc32fast::Hasher::new();h.update(&[0u8;4096]);println!("{}",crc32fast::__KIND.load(core::sync::atomic::Ordering::SeqCst));}' > "$W/k-$c/src/main.rs"
    k=$(cd "$W/k-$c" && RUSTFLAGS="${AF[$c]}" cargo run -q --release --target aarch64-unknown-linux-gnu $FE)
    if [ "$k" != "${AW[$c]}" ]; then echo "== $c: wrong kernel $k"; fail=1; continue; fi
    for t in patched pristine; do
      S=$TREE; [ $t = pristine ] && S=$W/pristine
      mkdir -p "$W/$t-$c/src"; cp "$HERE/harness/src/main.rs" "$W/$t-$c/src/"
      sed "s#SRC#$S#" "$HERE/harness/Cargo.toml.tmpl" > "$W/$t-$c/Cargo.toml"
      out=$(cd "$W/$t-$c" && RUSTFLAGS="${AF[$c]}" cargo run -q --release --target aarch64-unknown-linux-gnu $FE -- "$CASES" 2>&1 || true)
      echo "== $c kernel=$k $t: $(echo "$out" | grep -E '^ok|overflow case|panicked' | tr '\n' ' ')"
      echo "$out" | grep -q "^ok $CASES cases" || fail=1
      if [ $t = patched ]; then echo "$out" | grep -q "overflow case finalize=8cdc1683 8cdc1683" || fail=1; fi
      if [ $t = pristine ]; then echo "$out" | grep -q "attempt to add with overflow" || fail=1; fi
    done
  done
else
  echo "== aarch64 skipped: needs qemu-aarch64, aarch64-linux-gnu-gcc and the aarch64-unknown-linux-gnu rust target"
  [ -n "${VPIPE_REQUIRE_AARCH64:-}" ] && fail=1
fi
exit $fail
