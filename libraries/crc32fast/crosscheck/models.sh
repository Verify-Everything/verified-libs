#!/bin/bash
# Gate 8, models: run every CPU instruction that the hand-written Lean models stand for on random
# inputs (x86 on this CPU, aarch64 under qemu or a real arm64 CPU) and compare with the Lean
# models evaluated in the built variant projects. Usage: models.sh <dir holding the built variants>
set -uo pipefail
V=$(cd "$1" && pwd); HERE=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export PATH="$HOME/.elan/bin:$PATH"; fail=0
(cd "$HERE/models/x86gen" && CARGO_TARGET_DIR=$T/x cargo build -q --release) || exit 1
"$T/x/release/x86gen" 2000 > "$T/x86.txt" || { echo "x86gen failed (CPU lacks a feature?)"; exit 1; }
for v in x86_64 x86_64-std; do
  echo "== $v: $(cd "$V/$v" && lake env lean --run "$HERE/models/ModelCheck.lean" < "$T/x86.txt" | tail -1 | cut -c1-80)"
  (cd "$V/$v" && lake env lean --run "$HERE/models/ModelCheck.lean" < "$T/x86.txt" >/dev/null) || fail=1
done
if [ "$(uname -m)" = aarch64 ]; then RUN=""; TGT=""; else
  Q=$(command -v qemu-aarch64-static || command -v qemu-aarch64 || true)
  if [ -z "$Q" ] || ! command -v aarch64-linux-gnu-gcc >/dev/null; then
    echo "== aarch64 skipped: needs qemu-aarch64 and aarch64-linux-gnu-gcc"; [ -n "${VPIPE_REQUIRE_AARCH64:-}" ] && fail=1; exit $fail; fi
  export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_LINKER=aarch64-linux-gnu-gcc
  RUN="$Q -L /usr/aarch64-linux-gnu"; TGT="--target aarch64-unknown-linux-gnu"; fi
(cd "$HERE/models/a64gen" && CARGO_TARGET_DIR=$T/a cargo build -q --release $TGT) || exit 1
B=$(ls "$T"/a/*/release/a64gen "$T"/a/release/a64gen 2>/dev/null | head -1)
$RUN "$B" 20000 > "$T/a64.txt" || exit 1
for v in aarch64 aarch64-std; do
  echo "== $v: $(cd "$V/$v" && lake env lean --run "$HERE/models/ModelCheckA64.lean" < "$T/a64.txt" | tail -1)"
  (cd "$V/$v" && lake env lean --run "$HERE/models/ModelCheckA64.lean" < "$T/a64.txt" >/dev/null) || fail=1
done
exit $fail
