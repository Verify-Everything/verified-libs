#!/usr/bin/env bash
# Install Frama-C + Why3 + provers from nixpkgs and register provers with Why3. Idempotent.
# Usage: setup-framac.sh <space-separated nix packages> [pinned nixpkgs flake ref] [fallback ref]
set -euo pipefail
VH=${VPIPE_HOME:-$HOME/.vpipe}
mkdir -p "$VH/bin"
log() { echo "[setup-framac] $*" >&2; }

command -v nix >/dev/null || { log "ERROR: Frama-C setup needs Nix (https://nixos.org/download) or install frama-c, why3, z3, cvc5 yourself and put them on PATH"; exit 4; }
NIXPKGS=${2:-nixpkgs}
FALLBACK=${3:-}
mkdir -p "$VH/nix"
for p in $1; do
  # Pinned nixpkgs; --out-link makes a GC root so `nix store gc` never removes the tools.
  # Pick the main output's bin dir and symlink everything in it.
  out=$(nix --extra-experimental-features "nix-command flakes" build --out-link "$VH/nix/$p" --print-out-paths "$NIXPKGS#$p" | head -1) \
    || { [ -n "$FALLBACK" ] && out=$(nix --extra-experimental-features "nix-command flakes" build --out-link "$VH/nix/$p" --print-out-paths "tarball+$FALLBACK#$p" | head -1); }
  for b in "$out"/bin/*; do ln -sf "$b" "$VH/bin/"; done
done
export PATH="$VH/bin:$PATH"
why3 config detect >/dev/null 2>&1 || true
FV=$(frama-c -version | head -1)
PROVERS=$(why3 config list-provers 2>/dev/null | tr '\n' ';' || true)
log "Frama-C $FV; provers: $PROVERS"
CV=$(cbmc --version 2>/dev/null | head -1 || true)
echo "{\"frama_c\":\"$FV\",\"cbmc\":\"$CV\",\"why3_provers\":\"$PROVERS\",\"nixpkgs\":\"$NIXPKGS\"}"
