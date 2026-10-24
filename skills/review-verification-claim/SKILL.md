---
name: review-verification-claim
description: Adversarially review a verified-libs entry (CLAIM.md, spec, proofs, results) before admission, try to break the claim, and choose and run at least 10 planted bugs. Use when asked to review, audit or sign off a verification PR or claim card. Never use on an entry you helped prove.
---

# Adversarial review of a claim

You are the independent reviewer required by gate 10 of `STANDARDS.md`. Your job is to find
reasons the entry should NOT be admitted. Default to rejecting when unsure.

## Independence
- Start fresh. Read only the repo at the PR's head: `libraries/<lib>/` (CLAIM.md, specs, proofs,
  functions.toml, patches), `results/<lib>/latest.json`, `STANDARDS.md`, and the upstream
  source at the pinned commit. Do not read the prover's notes, chat logs or NOTES.md reasoning
  until you have written your own findings.
- If you (this session, or an agent you started) worked on the entry, stop and say so.

## Checks (record each as pass / fail with evidence)
1. **Real code.** Upstream URL, commit and archive SHA-256 match; patches are fixes with proofs,
   or tool-friendly rewrites with an equivalence proof. No model crate without a model-to-code proof.
2. **Every function.** Compare the engine's function list with your own scan of the pinned source,
   including trait impls, derives, every Cargo feature and every target (`cfg` branches, SIMD).
   Anything missing or open fails the entry.
3. **All inputs.** Look for size caps, bounded loops, `n <= MAX` preconditions, overflow
   assumptions that real callers can violate.
4. **Spec quality.** Read the spec without the proofs. Does it say what users expect? Is it
   checked against the governing standard or published test vectors? Try to write a wrong
   implementation that still meets the spec: if you can, the spec is too weak.
5. **Trusted base.** Run or read the axiom audit; every axiom and std model is listed in CLAIM.md
   and each model has a differential test. Grep for the forbidden constructs in STANDARDS.md.
6. **Cross-check.** A differential test of the translated code against the compiled upstream
   library exists and ran.
7. **Reproducibility.** Re-run `vkit run <lib>` from a clean checkout; numbers match the card.

## Planted bugs (you choose them; at least 10)
Pick bugs the author did not list, spread across functions: off-by-one bounds, wrong constants
or table entries, swapped operands, dropped edge cases (empty input, maximum size), wrong error
path, a change that only matters for large inputs. Apply each to a copy of the pinned source,
re-run extraction and the proofs, and confirm each one is rejected. A surviving mutant fails
the entry. Keep the list and outcomes.

## Output
Write `libraries/<lib>/REVIEW-<date>.md` (or a PR comment if the user prefers): verdict
(admit / reject), each check with evidence, the mutant table, and every issue found. Do not edit
proofs, specs or CLAIM.md yourself, and do not fill the maintainer's sign-off line.
