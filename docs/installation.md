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
3. copies the skills for the agents you pick (`--agents claude,codex,gemini`): Claude Code
   reads `~/.claude/skills/`; Codex and Gemini CLI both read `~/.agents/skills/`, so they share
   one copy. Any folder of the same name that vkit didn't install is backed up first,
4. optionally runs `vkit setup` for the tools you pick (`--tools`).
It prints the plan and asks first. `--dry-run` shows the plan only; `--yes` skips the questions.

## Agents
The skills follow the open Agent Skills format (a folder with `SKILL.md`), so one copy works in
Claude Code, Codex and Gemini CLI. Pick whichever way of installing suits you:

| Agent | Inside a clone of this repo | User-wide | As a package |
|---|---|---|---|
| Claude Code | reads `CLAUDE.md` (which imports `AGENTS.md`) | `vkit skills install --agent claude` | `/plugin marketplace add Verify-Everything/verified-libs` then `/plugin install verify-everything@verify-everything` |
| Codex | reads `AGENTS.md` and `.agents/skills/` | `vkit skills install --agent codex` | `codex plugin marketplace add Verify-Everything/verified-libs` then `codex plugin add verify-everything@verify-everything` |
| Gemini CLI | reads `GEMINI.md` (which imports `AGENTS.md`) and `.agents/skills/` once you trust the folder | `vkit skills install --agent gemini` | `gemini extensions install https://github.com/Verify-Everything/verified-libs` |

Tested on 2026-10-24 with Codex CLI 0.164.0 and Gemini CLI 0.65.0 in a clean home: each route
showed all eight skills (`codex debug prompt-input`, `gemini skills list`). Use one route per
agent, or the agent lists each skill twice. Codex shows the names and prompts from each skill's
`agents/openai.yaml`; other agents ignore that file. `vkit doctor` warns about old copies in
`~/.codex/skills/` from earlier vkit versions.

`vkit run <lib> --agent`, `run-all --agent` and `vpipe improve` hand work to a headless agent.
Pick it with `--agent-cli claude|codex|gemini` (or `VPIPE_AGENT_CLI`; default `claude`):

| CLI | Command the engine runs | Limits |
|---|---|---|
| claude | `claude -p ... --permission-mode acceptEdits --allowedTools <list>` | command allowlist, `--max-turns` |
| codex | `codex exec -s workspace-write --skip-git-repo-check -C <proj> --add-dir <dir>` | Codex's workspace-write sandbox; bounded by the engine's timeout |
| gemini | `gemini -p ... --approval-mode yolo --sandbox --include-directories <dir>` | runs only inside Gemini's sandbox (needs docker or podman) |

Results record which CLI ran (`agent_cli`). Whatever the agent writes is judged by the same proof
checks, axiom audit and protected gate. Status (2026-10-24): the codex and gemini command lines
were checked against both CLIs, which accept them; no end-to-end proof run with either has been
done yet, so report problems in a Toolchain problem issue.

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

## Pinned toolchain container
`container/Dockerfile` is the image CI re-checks every entry in (admission gate 9). It holds only
the tools; mount a checkout at `/work`:
```bash
docker pull ghcr.io/verify-everything/verified-libs-toolchain@<digest from toolchain/versions.toml>
docker run --rm -v "$PWD:/work" ghcr.io/verify-everything/verified-libs-toolchain@<digest> \
  python3 bin/vpipe.py run crc32fast
```
To build it yourself: `docker build -f container/Dockerfile -t verified-libs-toolchain .`. It is
big: about 19 GB unpacked (mathlib, Lean, Rust nightly, the Nix closure of Frama-C), so leave
30 GB free disk. Installing the tools and running the full engine gate inside it took 6 minutes
on 2026-10-24; writing the layer took longer. Behind a TLS-intercepting proxy add
`--secret id=ca,src=<ca.pem> --build-arg HTTPS_PROXY --build-arg APT_HTTPS=1`; the CA is used
during the build and not kept in the image.

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
