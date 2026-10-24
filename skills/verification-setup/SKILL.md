---
name: verification-setup
description: Install, check and repair the formal verification toolchain (Lean, elan, Aeneas, Charon, Rust nightly, mathlib cache, Frama-C, Why3, Z3, CVC5, CBMC) with vkit. Use when vkit doctor reports problems, a tool is missing, versions mismatch, or a network blocks downloads.
---

# Toolchain setup and repair

## Diagnose first
`vkit doctor` (or `vkit doctor --json`) lists tools, pinned versions, mathlib cache, reachable
hosts and problems. Fix only what the current task needs: a C task doesn't need Lean.

## Install
- `vkit setup lean`    Aeneas + Charon release, matching Rust nightly, elan, Lean, then mathlib cache
- `vkit setup mathlib` prebuilt mathlib, one shared copy in `~/.vpipe/lake/<key>/` linked into every project
- `vkit setup framac`  Frama-C + Why3 + Z3 + CVC5 via Nix (preferred) or opam
- `vkit setup cbmc`    GitHub .deb on Ubuntu/Debian x86_64, Homebrew on macOS, else Nix
Each prints a plan and asks. Pass `--yes` only when the user approved installs.
macOS/Windows: Aeneas ships Linux binaries only; use the dev container (`.devcontainer/`).

## Pins
All versions live in `toolchain/versions.toml`. They must agree: Lean = the Aeneas
release's `backends/lean/lean-toolchain`; Rust nightly = its `rust-toolchain`. Don't bump one
alone; `vpipe upgrade-tools` bumps Aeneas and keeps it only if the self-test gate passes.

## Restricted networks (seen in cloud sandboxes)
- release.lean-lang.org blocked: setup links the Lean release from github.com instead.
- cache.mathlib.org blocked: put a `lake-packages-<key>.tar.zst` from someone who has one in the
  repo's `cache/` (or a folder in `VPIPE_CACHE_DIRS`), or let mathlib compile (hours).
- opam.ocaml.org blocked: use Nix (cache.nixos.org) for Frama-C.
- api.github.com blocked: avoid `nix build github:...` flakes and `gh api`; plain git clone and
  release downloads from github.com still work.
- A directory mounted noexec: run scripts with `bash script.sh` / `python3 x.py`.
- `pkill -f <pattern>` can kill your own shell when the pattern is in the command line; use
  `ps` then `kill <pid>`.
