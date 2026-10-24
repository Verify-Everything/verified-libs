# Agent guide

This repo verifies open-source libraries. Read this before changing anything.

## Where things are
The repo root is the engine root.
- `bin/vpipe.py` the engine; `bin/vkit.py` toolkit CLI (doctor, setup, skills; the rest goes to vpipe).
- `libs/<library>/<version>/` admitted entries; `candidates/<library>/<version>/` work below the bar.
- `libraries/<lib>/` the engine's working folder per library: `vpipe.toml` manifest, proofs, `NOTES.md`,
  optional `functions.toml` (theorem mapping, verified fixes) and `patches/`.
- `results/<lib>/latest.json` run outputs; `results/SUMMARY.md`.
- `notes/general.md` lessons from every library (read first). `toolchain/versions.toml` pins.
- `self/gate.py` + `selftest/` protected acceptance gate; `templates/`, `checklists/` engine data.
- `skills/` agent skills, shared by Claude Code, Codex and Gemini CLI (`.agents/skills` links here;
  `.claude-plugin/`, `plugin.json` + `.agents/plugins/`, `gemini-extension.json` package them).
  Start with `skills/verify-library/SKILL.md`. `CLAUDE.md` and `GEMINI.md` only import this file.
- `docs/` human docs. `install.sh` installer.

## Finish line
A library is finished only when every function in the pinned upstream source is verified or has
a verified fix (`Functions N/N` in results). Nothing is "out of scope". Never describe N/M < N/N
as complete.

## Admission
Strict, per `STANDARDS.md` (ten gates, no waivers). Every entry has
`libraries/<lib>/CLAIM.md`; success criteria are approved by the maintainer before proof work;
only `full-correctness` on every function admits; model crates and tool-friendly patches need
equivalence proofs. Agents never fill Review lines, never set Status to verified, and never
review an entry they worked on.

## Rules
1. Never weaken a claim to make it pass: no `sorry`, `admit`, new `axiom`, `native_decide`,
   `bv_decide`, no deleting a scope property, no editing `*/Extracted/`.
2. Never edit `self/gate.py` or `selftest/` together with the code they judge.
3. Keep pins consistent: change versions only in `toolchain/versions.toml`, and only
   through `vpipe upgrade-tools` or with `vkit selftest --full` passing.
4. Ask the user before: installing system packages, pushing, opening PRs, filing upstream issues.
   `vkit setup` prints a plan; pass `--yes` only after the user approved.
5. Report exactly what ran and what it showed. Distinguish proved, bounded-checked, tested and
   assumed. Leave unknowns as unknowns.
6. Don't commit build outputs or caches. Don't vendor upstream source; patch files only.
7. Record lessons that help the next library in `notes/general.md` under a dated heading.
8. A PR touches one library folder, or the engine/toolkit, not both.

## Commands
```
vkit doctor | vkit setup lean|framac|cbmc|mathlib
vkit new <lib> --lang rust|c --upstream URL --commit SHA --version TAG
vkit run <lib> [--extract-only] [--agent] | vkit run-all | vkit report | vkit selftest [--full]
```
