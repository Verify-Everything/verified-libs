#!/usr/bin/env bash
# Install Frama-C + Why3 + provers from nixpkgs and register provers with Why3. Idempotent.
# Usage: setup-framac.sh <space-separated nix packages>
set -euo pipefail
VH=${VPIPE_HOME:-$HOME/.vpipe}
mkdir -p "$VH/bin"
log() { echo "[setup-framac] $*" >&2; }

command -v nix >/dev/null || { log "ERROR: Frama-C setup needs Nix (https://nixos.org/download) or install frama-c, why3, z3, cvc5 yourself and put them on PATH"; exit 4; }
for p in $1; do
  # Pick the main output's bin dir and symlink everything in it.
  out=$(nix --extra-experimental-features "nix-command flakes" build --no-link --print-out-paths "nixpkgs#$p" | head -1)
  for b in "$out"/bin/*; do ln -sf "$b" "$VH/bin/"; done
done
export PATH="$VH/bin:$PATH"
why3 config detect >/dev/null 2>&1 || true
FV=$(frama-c -version | head -1)
PROVERS=$(why3 config list-provers 2>/dev/null | tr '\n' ';' || true)
log "Frama-C $FV; provers: $PROVERS"
echo "{\"frama_c\":\"$FV\",\"why3_provers\":\"$PROVERS\"}"
