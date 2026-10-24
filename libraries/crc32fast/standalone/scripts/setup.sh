#!/usr/bin/env bash
# Install the pinned toolchain into $TOOLS (default ~/tools). Idempotent.
# Downloads only from github.com releases and static.rust-lang.org, because
# release.lean-lang.org, api.github.com and cache.mathlib.org may be blocked.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"; source "$here/pins.env"
TOOLS="${TOOLS:-$HOME/tools}"; mkdir -p "$TOOLS"

if [ ! -x "$TOOLS/aeneas-$AENEAS_RELEASE/aeneas" ]; then
  d="$TOOLS/aeneas-$AENEAS_RELEASE"; mkdir -p "$d"
  curl -sSfL -o "$d/aeneas.tgz" "https://github.com/AeneasVerif/aeneas/releases/download/$AENEAS_RELEASE/aeneas-linux-x86_64.tar.gz"
  echo "$AENEAS_TARBALL_SHA256  $d/aeneas.tgz" | sha256sum -c -
  tar -C "$d" -xzf "$d/aeneas.tgz" && rm "$d/aeneas.tgz"
fi

rustup toolchain install "$RUST_NIGHTLY" --profile minimal -c rustc-dev,llvm-tools,rust-src,miri
rustup target add --toolchain "$RUST_NIGHTLY" "$CHARON_TARGET"

if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
fi
if ! "$HOME/.elan/bin/elan" toolchain list | grep -q "v$LEAN_VERSION"; then
  command -v zstd >/dev/null || (apt-get install -y -qq zstd || sudo apt-get install -y -qq zstd)
  curl -sSfL "https://github.com/leanprover/lean4/releases/download/v$LEAN_VERSION/lean-$LEAN_VERSION-linux.tar.zst" | tar -C "$TOOLS" --zstd -x
  "$HOME/.elan/bin/elan" toolchain link "leanprover--lean4---v$LEAN_VERSION" "$TOOLS/lean-$LEAN_VERSION-linux"
fi
echo "toolchain ready"
