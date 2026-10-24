# Installation

## Requirements
- git, curl, Python 3.11+
- Linux x86_64 or aarch64 for the Rust/Lean stack (Aeneas ships Linux binaries only).
  macOS and Windows: use the dev container.
- Disk: ~10 GB for Lean + mathlib; RAM: 8 GB minimum, 16 GB comfortable.

## One command
```bash
curl -fsSL https://raw.githubusercontent.com/Verify-Everything/verified-libs/main/install.sh | bash
```
or from a checkout: `bash install.sh`. The installer:
1. clones the repo to `~/verified-libs` (or uses the checkout it runs from; `--dir` to change),
2. writes `~/.vpipe/bin/vkit` and `~/.vpipe/bin/vpipe` and adds `~/.vpipe/bin` to PATH,
3. copies the skills to `~/.claude/skills/` and/or `~/.codex/skills/` (`--agents`),
   backing up any folder of the same name that vkit didn't install,
4. optionally runs `vkit setup` for the tools you pick (`--tools`).
It prints the plan and asks first. `--dry-run` shows the plan only; `--yes` skips the questions.

## Tools one at a time
| Command | Installs | Where |
|---|---|---|
| `vkit setup lean` | Aeneas + Charon release, Rust nightly for Charon, elan, Lean; then the mathlib cache | `~/.vpipe`, `~/.rustup`, `~/.elan` |
| `vkit setup mathlib` | prebuilt mathlib for the pinned Lean (one shared copy, linked into every project) | `~/.vpipe/lake/<key>/` |
| `vkit setup framac` | Frama-C, Why3, Z3, CVC5 via Nix (or opam) | Nix store, linked into `~/.vpipe/bin` |
| `vkit setup cbmc` | CBMC (GitHub .deb, Homebrew, or Nix) | system / Nix |

All versions come from `toolchain/versions.toml`. Override locations with `VPIPE_HOME`,
`VPIPE_WORK`, `VPIPE_NOTES` and `VPIPE_CACHE_DIRS`. `vkit doctor` compares what is
installed with the pins.

## Dev container (macOS, Windows, or a clean Linux box)
Open the repo in VS Code with the Dev Containers extension, or in GitHub Codespaces, and
choose "Reopen in Container". `postCreateCommand` runs the installer with all tools. Or:
```bash
devcontainer up --workspace-folder .
```

## Restricted networks
Some sandboxes block hosts. `vkit doctor` shows which. Workarounds the engine already uses:
- `release.lean-lang.org`: Lean comes from the GitHub release instead.
- `cache.mathlib.org`: put someone's `lake-packages-<key>.tar.zst` in the repo's `cache/` (or a
  folder named in `VPIPE_CACHE_DIRS`); otherwise mathlib compiles from source (hours).
- `opam.ocaml.org`: use Nix for Frama-C.
- `api.github.com`: avoid `nix build github:...` and `gh api`; git clones and release
  downloads from github.com still work.

## Update and remove
- `vkit update` pulls the checkout and refreshes installed skills.
- Remove: delete `~/.vpipe`, the skill folders listed by `vkit doctor`, and the PATH line in your
  shell rc. Rust toolchains and elan are shared with other tools; remove them with `rustup` / `elan`
  if you want.
