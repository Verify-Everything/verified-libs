---
name: verify-library
description: Formally verify an open-source library end to end with the vkit/vpipe toolkit (Rust via Aeneas+Lean, C via Frama-C WP and CBMC). Use when asked to verify, prove correct, or add a library to Verify-Everything/verified-libs, or to re-check one after an upstream release.
---

# Verify a library

You are working in a checkout of `Verify-Everything/verified-libs`. The repo root is the engine
root: `bin/vpipe.py` is the engine, `bin/vkit.py` wraps it and adds `doctor`, `setup` and `skills`.
Each library lives in one folder, `libraries/<lib>/` (manifest `vpipe.toml`, proofs, notes,
optional `functions.toml`). Everything below runs from the repo root.

## The finish line
**A library is finished only when every function in the pinned upstream source is verified or
has a verified fix.** The engine scans every function (including trait impls and code behind
`cfg` for other targets) and reports `Functions N/M`; status says "complete" only at N/N.
There is no "out of scope": an unsupported or skipped function stays open until it is handled
(a patch proved equivalent to the original, a model with a model-to-code proof, a verified fix,
or a second tool). Partial results are welcome as candidate PRs: say "N/M functions at
full-correctness" and never call them verified or finished.

## 0. Ready check (once per machine)
Run `vkit doctor`. If tools are missing, use the **verification-setup** skill. Don't reinstall
tools on every task.

## 1. Pick and pin
- Target fit: widely used, small to medium (under ~5k lines in the verified part), no public
  verification attempt. Use **pick-verification-target** if the user has not named one.
- Pin a release tag and its full commit hash. Never verify a moving branch.
- Check `libraries/` and open PRs first so two people don't take the same library.

## 1b. Admission is strict: read STANDARDS.md first
Only entries passing all ten gates are called verified; everything else goes under
`candidates/`. The ones that change how you work:
- **Real code only.** Prove the pinned upstream source. A tool-friendly patch must be proved
  equivalent to the original; a model crate counts only with a model-to-code equivalence proof.
- **Every function, feature and target**, SIMD paths and trait impls included, **all inputs**
  (no bounds, no size caps), **at `full-correctness`**. Labels: `full-correctness`,
  `safety-contracts`, `no-ub`, `bounded`, `tested`; the entry takes the weakest.
- **Spec and success criteria first.** `vkit new` writes `libraries/<lib>/CLAIM.md` from
  [templates/CLAIM.md](templates/CLAIM.md). Fill "Success criteria" and "Specification: plain
  words", open a draft PR with only the manifest and card, and wait for the maintainer to
  approve before writing proofs. Changing them later needs a new review.
- **Not vacuous.** Check the spec against the governing standard or published test vectors. The
  reviewer picks at least 10 planted bugs; each must break the proof.
- **Cross-check the translation** with a differential test against the compiled upstream crate.
- **Two reviews.** Maintainer sign-off plus a fresh adversarial review agent with no access to
  your notes (the **review-verification-claim** skill, run in a new session). You (and any agent working for you) never sign off your own entry.

## 2. Scaffold
```
vkit new <lib> --lang rust|c --upstream <git url> --commit <sha> --version <tag>
```
This writes `libraries/<lib>/vpipe.toml` and the proof project beside it from templates.
In the manifest comment, record the prior-work search (where you looked, what you found).

## 3. Extract or first pass before writing any spec
- Rust: `vkit run <lib> --extract-only`. Read the skipped and unsupported items in
  `results/<lib>/latest.json`. They decide the scope. Fixes that worked before are in
  [references/scoping.md](references/scoping.md).
- C: run CBMC first (**cbmc-bounded-checks**): fast, no annotations, finds real bugs. Then
  Frama-C WP on the functions worth an unbounded proof (**framac-wp-proofs**).

## 4. Specs: headline properties plus every function
- Fill `[scope].properties` with the 2-5 statements users care most about (round trip, matches a
  reference, no overflow, no out-of-bounds, no UB).
- Then cover every function in `results/<lib>/latest.json` → `functions`: each needs a proved
  theorem that specifies it (Lean) or proved WP goals plus an `ensures` contract (C). Small
  helpers usually fall out of the headline proofs; give each its own step theorem anyway.
- For a model crate, map each upstream function to the theorems that cover it in
  `libraries/<lib>/functions.toml` (`id`, `theorems`).
- For a function with a bug: write the fix as `patches/<name>.patch`, verify the fixed version,
  and record `status = "fixed"` with `fix = ...` in `functions.toml`. Draft the upstream issue.
- `[scope].exclusions` lists assumptions only (std models, overflow bounds, tool-friendly
  rewrites), not skipped functions.

## 5. Prove
- By hand with the tool skill (**lean-aeneas-proofs** or **framac-wp-proofs**), or
- `vkit run <lib> --agent [--agent-cli claude|codex|gemini]` to let a headless agent iterate (up to 3 build/fix rounds).
Re-run `vkit run <lib>` until the result is green, then keep going until `Functions` is N/N. A theorem counts as proved only if its
axioms are propext, Classical.choice and Quot.sound (the engine audits this). Never add
`axiom`, `sorry`, `admit`, `native_decide` or `bv_decide` to a claimed result.

## 6. Check the proofs are not vacuous
Plant small bugs in a copy of the source (off-by-one, wrong constant, flipped comparison) and
confirm each breaks a proof. Do 5+ yourself early; for admission the reviewer picks at least 10
and every one must be rejected. Record mutants and outcomes in CLAIM.md.

## 7. Report and submit
- Complete CLAIM.md from the result JSON: Code, Proof (tools, per-function labels in
  functions.toml, planted-bug count, cross-check), Trusted base, Not covered (must be empty for
  verified), Bugs and fixes. Leave Status at `candidate` and the Review lines empty: reviewers
  fill them.
- `vkit report` rebuilds `results/SUMMARY.md` (Functions N/M and every open function).
- Write `libraries/<lib>/NOTES.md` (status, Functions N/M, properties, assumptions, how to re-run)
  and add cross-library lessons to `notes/general.md` under a dated heading.
- If you found a bug, draft an upstream issue in `libraries/<lib>/upstream-issue.md`
  and ask the user before filing it.
- Open the PR with **submit-verification-results**.

## Rules
- Don't edit anything under `*/Extracted/`; it is regenerated every run.
- Keep source rewrites as patch files referenced from the manifest, and run the upstream test
  suite on the patched code.
- Keep claims exact: say "proved for all inputs", "checked for lengths 0..32", or "open".
- CBMC bounded checks and tests are evidence, not verification: a function checked only by CBMC
  stays open and the entry is at most a candidate.
- Forbidden in claimed proofs (CI fails): `sorry`, `admit`, new `axiom`, `native_decide`,
  `bv_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque` in specs, kernel-skipping
  options; Frama-C `admit`, unproved goals, runs without `-wp-rte`.
