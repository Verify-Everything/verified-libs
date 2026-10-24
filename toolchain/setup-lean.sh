#!/usr/bin/env bash
# Install the Rust -> Lean stack (Aeneas, Charon, Rust nightly, elan, Lean). Idempotent.
# Usage: setup-lean.sh <aeneas_tag> <aeneas_url> <lean_version> <lean_url> <elan_init_url> <rust_components_csv>
set -euo pipefail
TAG=$1; AURL=$2; LEANV=$3; LURL=$4; ELAN_INIT=$5; RCOMP=$6
VH=${VPIPE_HOME:-$HOME/.vpipe}
mkdir -p "$VH/bin" "$VH/toolchains"
log() { echo "[setup-lean] $*" >&2; }

NIXF=(--extra-experimental-features "nix-command flakes")   # default Nix installs lack these
# zstd unpacks the Lean tarball and the mathlib cache. Try, in order: present, Nix, brew, apt.
if ! command -v zstd >/dev/null; then
  if command -v nix >/dev/null; then
    ln -sf "$(nix "${NIXF[@]}" build --no-link --print-out-paths nixpkgs#zstd.bin)/bin/zstd" "$VH/bin/zstd"
  elif command -v brew >/dev/null; then
    brew install zstd >&2
  elif command -v apt-get >/dev/null; then
    SUDO=""; [ "$(id -u)" -ne 0 ] && SUDO="sudo"
    $SUDO apt-get update -qq >&2 && $SUDO apt-get install -y -qq zstd >&2
  else
    log "ERROR: install zstd (https://github.com/facebook/zstd) and re-run"; exit 4
  fi
fi
export PATH="$VH/bin:$PATH"

# 1. Aeneas + Charon release tarball.
AD="$VH/aeneas-$TAG"
if [ ! -x "$AD/aeneas" ]; then
  log "downloading Aeneas $TAG"
  mkdir -p "$AD.tmp" && curl -fsSL "${AURL//\{tag\}/$TAG}" | tar xz -C "$AD.tmp" && mv "$AD.tmp" "$AD"
fi
ln -sfn "$AD" "$VH/aeneas"

# 2. Lean version must match the Aeneas library.
WANT=$(sed 's/.*://; s/^v//' "$AD/backends/lean/lean-toolchain")
if [ "$WANT" != "$LEANV" ]; then
  log "ERROR: versions.toml lean=$LEANV but Aeneas $TAG wants $WANT"; exit 3
fi

# 3. Rust nightly that Charon was built against.
CHAN=$(sed -n 's/^channel *= *"\(.*\)"/\1/p' "$AD/rust-toolchain")
if ! rustup toolchain list | grep -q "^$CHAN"; then
  log "installing Rust $CHAN"
  rustup toolchain install "$CHAN" --profile minimal -c "$RCOMP" >&2
fi
# riscv64 no_std target lets Charon skip SIMD/arch code without source edits (see general.md).
rustup target add --toolchain "$CHAN" riscv64gc-unknown-none-elf >&2 2>/dev/null || true

# 4. elan + Lean (release.lean-lang.org is blocked, so link a GitHub release).
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  log "installing elan"
  curl -fsSL "$ELAN_INIT" | sh -s -- -y --default-toolchain none >&2
fi
if ! "$HOME/.elan/bin/elan" toolchain list | grep -q "v$LEANV"; then
  # Normal route first; on networks that block release.lean-lang.org, link the GitHub release.
  "$HOME/.elan/bin/elan" toolchain install "leanprover/lean4:v$LEANV" >&2 2>/dev/null || true
fi
if ! "$HOME/.elan/bin/elan" toolchain list | grep -q "v$LEANV"; then
  log "downloading Lean $LEANV from GitHub"
  U=${LURL//\{version\}/$LEANV}
  curl -fsSL "$U" | zstd -dc | tar x -C "$VH/toolchains"
  "$HOME/.elan/bin/elan" toolchain link "leanprover/lean4:v$LEANV" "$VH/toolchains/lean-$LEANV-linux" >&2
fi

echo "{\"aeneas\":\"$TAG\",\"charon_rust\":\"$CHAN\",\"lean\":\"$LEANV\",\"aeneas_dir\":\"$AD\"}"
