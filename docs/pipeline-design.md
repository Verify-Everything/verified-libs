# Verification pipeline design

Owner: analysis thread "Streamline the verification pipeline". Status: **v1, built and tested** (2026-10-24 ~04:45 UTC).
The pipeline itself lives in `/mnt/project-files/pipeline/` (start with its README.md).

## 1. What the threads repeat (evidence from notes so far)

| Repeated step | Seen in | Cost each time | Now handled by |
|---|---|---|---|
| Find a toolchain that installs past the network blocks (opam, release.lean-lang.org, api.github.com, cache.mathlib.org all refused) | crc32fast, semver, percent-encoding, Neovim | 20-60 min of trial and error | `vpipe setup` (pinned, ~1.5 min from a clean home) |
| Match Aeneas, Charon, Rust nightly, Lean and mathlib versions | all three Rust threads | high, and easy to get wrong | `toolchain/versions.toml`, setup checks they agree |
| Build mathlib from source | all Rust threads | hours | auto-restore of the shared tarball in `verification-notes/cache/`; publish one after any from-source build |
| zstd missing, /mnt/project-files noexec | crc32fast, percent-encoding, Neovim | minutes | setup script / bootstrap |
| Frama-C without WP from apt; alt-ergo unfree in nixpkgs | Neovim, inih | 10+ min | `setup-framac.sh` (Nix: Frama-C 33, Why3, Z3, CVC5) |
| Charon target tricks (riscv64 no_std, `--sysroot default`) | crc32fast, percent-encoding | 10-30 min | manifest fields + template comments |
| Aeneas unsupported features decide scope (early return in loop, closures, nested mutable borrows, unsafe packing) | percent-encoding, semver | hours if found late | `vpipe run --extract-only` lists every skipped item in the result before any spec is written |
| Std functions modelled by axioms in `FunsExternal_Template.lean` | percent-encoding | easy to forget they are assumptions | copied to `<Module>/External/` once, counted as "Axioms" on SUMMARY.md |
| Keeping annotations or source rewrites across releases | Neovim, percent-encoding | manual | overlay folder today; patch files on the backlog |

## 2. What was built

```
vpipe setup [lean|framac]      pinned toolchains, idempotent
vpipe new <lib> ...            manifest + proof project from templates
vpipe run <lib> [--agent] [--extract-only] [--improve]
                               fetch pinned commit -> extract -> prove -> results/<lib>/latest.json
vpipe run-all                  every manifest (use after an upstream or tool bump)
vpipe report                   results/SUMMARY.md: proved, sorries, axioms, skipped, per-function table
vpipe selftest / self/gate.py  fixtures: a C file (13/13 WP goals) and a Rust crate proved in Lean
vpipe improve [--goal] [--propose]
                               self-update: an agent reads notes, results and the backlog, changes the
                               pipeline, the protected gate keeps or rolls back, logged in self/CHANGELOG.md
vpipe upgrade-tools            tries the newest Aeneas nightly; kept only if the full gate passes
vpipe rollback                 restores the last snapshot
bootstrap.sh                   fresh container -> tools installed -> gate passed
```

`--agent` hands the proof stage to a headless Claude session with a tool-specific prompt
(`templates/prompts/`), for up to 3 build/fix rounds.

### Self-update and self-implementation
- **Update itself:** `vpipe improve` (or `run --improve`) reads general.md, per-library notes, results and
  `self/BACKLOG.md`, picks the highest-value change, makes it, and writes what/why/evidence to
  `self/CHANGELOG.md`. `upgrade-tools` keeps the toolchain pin current.
- **Implement itself:** `vpipe improve --goal "<feature>"` builds a requested feature into the pipeline;
  `bootstrap.sh` rebuilds a working install from nothing.
- **Guardrails:** the agent may only edit code, templates and logs. Proofs, results, manifests, the notes
  folder, the gate and its fixtures are protected, so a change cannot weaken the test that judges it.
  Every change is snapshotted first; a failed gate restores the snapshot and logs the rollback. A lock
  stops two sessions self-updating at once. It never pushes, opens PRs or creates repositories.

### Tested so far
- Clean-home bootstrap: 1 min 38 s, gate passes.
- inih (Frama-C, no annotations yet): 27/74 goals, 6 min; per-function table shows where to start.
- percent-encoding (extract only): runs, 13 unsupported items and 36 assumed std functions listed.
- Lean fixture with the shared mathlib cache: restore + build in about 45 s.
- `vpipe improve` in a test copy added the per-function table on its own; the gate kept it.
- A planted bad change (WP count forced to 0) failed the gate and was rolled back.
- `vpipe improve` on the live pipeline added a Lean axiom audit (v0.1.1): a theorem counts as proved only if
  it rests on Lean's three standard axioms. Negative test: a theorem built on `axiom cheat : False` is flagged,
  a `sorry` is flagged, the real one passes. Lesson taken: improve now runs the full Lean gate whenever the
  mathlib cache exists, because the quick gate had let this change in untested.

## 3. New-library checklist
See `pipeline/checklists/new-library.md`. Short form: check fit -> pick tool -> pin commit ->
`vpipe new` -> `vpipe run --extract-only` and read what was skipped -> write 2-5 scope properties ->
prove (by hand or `--agent`) -> notes -> add anything done by hand to the backlog.

## 4. Open items (also in pipeline/self/BACKLOG.md)
- CBMC first pass and mutation check for C (Neovim's method); Frama-C `Typed+Cast` / `-DNDEBUG` options.
- Adopt each finished thread's proofs into `pipeline/proofs/<lib>/` so `run-all` re-checks them on new releases.
- Network: allowing `cache.mathlib.org`, `release.lean-lang.org` and `api.github.com` in the environment settings would remove the biggest workarounds (crc32fast thread already asked Yerin).

## 5. Completion rule (Yerin, 2026-10-24)
A library is finished only when **every function** in the pinned upstream source is verified or has a
verified fix. The pipeline enforces it:
- Each run scans the upstream source (not the patched copy or model crate) for every function, including
  ones behind `cfg` for other targets and trait impls. C: every function definition in the listed files.
- Status per function, from evidence: **verified** (Lean: every theorem that mentions it is proved with
  standard axioms only; C: all its WP goals proved and it has an `ensures` contract), **fixed** (same, plus
  `status = "fixed"` and the fix patch in `functions.toml`), otherwise **open** with the reason.
  There is no "out of scope" status.
- `results/SUMMARY.md` shows Functions N/M and lists every open function. Status says "complete" only at N/N.
- `libraries/<lib>/functions.toml` lets a thread point a function at its theorems (needed for model crates)
  or record a fix.
- Current: crc32fast 9/43, percent-encoding 9/26, semver 4/92 (model functions still need mapping).

## 6. Repo layout for Verify-Everything/verified-libs
The repo is the pipeline root, so `vpipe` runs straight from a clone.
```
verified-libs/
  README.md  CONTRIBUTING.md  LICENSE  VERSION  bootstrap.sh
  bin/ toolchain/ templates/ checklists/      the engine (vpipe)
  self/  (gate.py, CHANGELOG.md, BACKLOG.md)  self-update; gate + selftest/ owned by maintainers (CODEOWNERS)
  selftest/                                   fixtures the gate proves
  libraries/<lib>/                            ONE FOLDER PER LIBRARY
    vpipe.toml          manifest: upstream, pinned commit, tool, scope, patches, tests
    functions.toml      per-function evidence and fixes (optional)
    README.md / NOTES.md what is proven, assumptions, findings
    ...                 Lean project (lakefile.lean.tmpl, <Module>/...) or src/ (annotated C), patches/, rust/
  results/<lib>/latest.json, results/SUMMARY.md   written by CI, not by hand
  docs/lessons.md                             curated from verification-notes/general.md
  .github/workflows/verify.yml                gate on every PR; run changed libraries; scheduled run-all
```
- Forks (`Verify-Everything/<lib>`) only when we fix an upstream bug; tool-friendly rewrites stay as
  `libraries/<lib>/patches/*.patch` (checked by the library's tests).
- Not committed: `.lake/`, `target/`, `self/snapshots/`, caches. The mathlib tarball is too big for git;
  CI restores it from a release asset or uses `lake exe cache get` on an open network.
- Self-update in a shared repo: `vpipe improve` must land as a branch + PR, never a direct push.

## 7. What a contributor-facing install needs from the pipeline (for the toolkit thread)
Done in the engine:
- Paths: everything relative to the clone; `VPIPE_HOME` (tools, default ~/.vpipe), `VPIPE_WORK` (checkouts),
  `VPIPE_NOTES` (lessons; falls back to notes/ in the repo), `VPIPE_CACHE_DIRS` (mathlib tarballs).
- Normal-network routes first: `elan toolchain install`, then GitHub release; `lake exe cache get` before
  compiling mathlib; zstd via nix, brew or apt (with sudo); Nix flags passed explicitly.
- One shared mathlib per cache key under `$VPIPE_HOME/lake/`, symlinked into each project (2.4 GB once).
- Setup retries, and subprocesses never inherit a fragile working directory.
Still needed (backlog):
- macOS: Aeneas also ships `aeneas-macos-aarch64`; setup picks linux-x86_64 only.
- Frama-C without Nix (opam or Docker); CBMC setup (toolkit has tested templates to lift).
- CI workflow and CODEOWNERS for the gate; `vpipe improve` opening a PR instead of editing in place.
- Fixed contribution format: a PR adds `libraries/<lib>/` (vpipe.toml + proofs); CI writes results. The
  result JSON schema is the one in results/*/latest.json (library, commit, toolchain, extract, prove,
  functions).

## Changelog
- v1.5 (06:00): every-function completion rule enforced; repo layout for verified-libs; contributor install needs; one folder per library; shared mathlib.
- v1.4 (05:35): inih and Neovim Frama-C lessons folded in (v0.1.4); Helix thread noted, using the same model-crate method as semver.
- v1.3 (05:25): percent-encoding runs natively in vpipe (49/49, tests and differential test included); pipeline v0.1.3 adds patches, test commands, fix-up hooks.
- v1.2 (05:15): crc32fast adopted by its thread (132/132 proved via `vpipe run`, about 1-3 min); its three gaps fixed in pipeline v0.1.2.
- v1.1 (04:55): axiom audit added by the pipeline itself and verified; improve now uses the full gate.
- v1 (04:45): pipeline built and tested; table of repeated steps from four threads' notes.
- v0 (03:50): skeleton from first principles and container check.
