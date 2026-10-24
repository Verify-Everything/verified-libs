# Contributing to verified-libs

Thanks for wanting to add receipts. There are four kinds of contribution, from smallest to largest:

1. **Report a toolchain problem** (setup fails, pins disagree, a host is blocked): open a
   "Toolchain problem" issue with `vkit doctor --json` output.
2. **Submit or claim a library**: open a "Submit a library" issue with the library, version, tool
   and your success criteria. It records the prior-work search, gets the criteria approved before
   you invest effort, and stops two people verifying the same thing.
3. **Verify a library**: add a manifest, proofs and notes; open a PR. Most contributions.
4. **Improve the engine or skills**: `bin/`, `toolchain/`, `templates/`, `skills/`, `docs/`.

## Admission is strict
verified-libs aims to be a standard people can rely on when attackers use AI too. Entries are
admitted only if they pass all ten gates in [docs/standards.md](docs/standards.md), with no
waivers: the real upstream code, every function/feature/target, all inputs, full functional
correctness, spec and success criteria approved before work starts, at least 10 planted bugs
caught, a clean trusted base, a differential cross-check of the translation, reproducible CI, and
two reviews (the maintainer and a fresh adversarial review agent; never the author). Work that
doesn't pass yet is welcome as a candidate.

## The finish line
A library is **finished only when every function in the pinned upstream source is verified or
has a verified fix**. The engine lists every function and shows `Functions N/M`; it says
"complete" only at N/N. There is no "out of scope". Partial work is welcome as a PR (it moves
the count), labelled with its N/M.

## Set up
```bash
git clone https://github.com/<you>/verified-libs && cd verified-libs
bash install.sh            # asks before each change
vkit doctor
```
Details per platform: [docs/installation.md](docs/installation.md).

## Verify a library
First write the "Success criteria" and "Specification" parts of `libraries/<lib>/CLAIM.md` and
open a draft PR so the maintainer can approve them. Then:
Follow [docs/adding-a-library.md](docs/adding-a-library.md), or ask your agent to use the
`verify-library` skill. In short: pin a commit, `vkit new`, `vkit run --extract-only`, write
2-5 headline properties, prove them, then cover every remaining function, run the mutation
check, write notes, `vkit report`, open a PR.

## What a PR must show
- A PR adds or changes one folder, `libraries/<lib>/`. CI re-runs it and writes
  `results/<lib>/latest.json`; you don't need to commit results by hand.
- `vkit run <lib>` passes from a clean checkout; paste the summary from
  `results/<lib>/latest.json` (Functions N/M, proved/total, sorries, axioms).
- Exact claims: "proved for all inputs", "checked for lengths 0..32", "assumes X". Every
  assumption (std models, tool-friendly patches, overflow bounds) is in the manifest's
  `exclusions`. Exclusions are assumptions, never skipped functions.
- No `sorry`, `admit`, new `axiom`, `native_decide` or `bv_decide` in claimed theorems. The axiom
  audit enforces this; don't work around it.
- No build outputs (`.lake/`, `target/`, caches, tarballs).
- Engine changes: `vkit selftest --full` passes, and the change has a line in
  `self/CHANGELOG.md`. Don't edit `self/gate.py` or `selftest/` in the same PR as the change
  they would judge (CODEOWNERS requires a maintainer for those).

## AI-assisted work
Welcome, including proofs written entirely by an agent. A human owns every PR: you have read
the final diff, you can explain the spec (the spec is what a reader trusts, so review it more
carefully than the proofs), and you checked the evidence. Agents must not tick the human-owner
boxes in the PR template.

## Where entries live
Admitted entries: `libs/<library>/<version>/` (CLAIM.md, spec/, proof/, pipeline/run.sh). Work below
the bar: `candidates/<library>/<version>/`, same shape. The vpipe engine works in
`libraries/<lib>/` today; an entry is copied into `libs/` or `candidates/` when it is submitted.
Run both checks before a PR:
```bash
python3 scripts/check_structure.py   # layout and claim cards
python3 scripts/check-repo.py        # skills, manifests, forbidden constructs
```

## Upstream bugs
If verification finds a bug, the function counts once the fix is verified: put the fix in
`libraries/<lib>/patches/`, record `status = "fixed"` in `functions.toml`, and write the report in
`libraries/<lib>/upstream-issue.md` (minimal reproduction, affected versions, suggested fix).
If upstream doesn't take the fix, the project forks the library as `Verify-Everything/<lib>`. Maintainers file
it upstream after review, so the project speaks with one voice and reports are checked first.

## Found an unsound or overstated claim?
That counts as a security issue for this project. Report it privately, as described in the org's
security policy, rather than in a public issue. A bug in verified code is handled as a security
incident: upstream is told privately first, then the entry is revoked publicly.

## Standards changes
Use the *Propose a standards change* issue form. [STANDARDS.md](STANDARDS.md) is approved; changes
need the maintainer's approval.

## Style
- Lean: follow the patterns in `skills/lean-aeneas-proofs/`; one step theorem per Rust function,
  specs independent of the Rust code.
- C: ACSL as a patch or annotated copy; the annotation-only check must pass.
- Notes: short dated sections; put lessons that help other libraries in
  `notes/general.md`.

## Conduct
Participation is covered by the org's Code of Conduct. Be precise and credit others' work.
Disagreements about whether something is proved are settled by the checker, not by argument.
