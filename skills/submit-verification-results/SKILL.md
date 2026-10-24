---
name: submit-verification-results
description: Package verification work (manifest, proofs, results, notes) as a pull request to Verify-Everything/verified-libs with honest claims and reproducible evidence. Use when a library's proofs are ready to share or when updating results after an upstream release.
---

# Submit results

## Before opening the PR
0. Read `STANDARDS.md`. Only an entry passing all ten gates may say "verified"; anything
   else is submitted as a candidate. `libraries/<lib>/CLAIM.md` is complete, its success criteria
   were approved by the maintainer before the proof work, and functions.toml gives every function
   a label and its theorem. Leave Status `candidate` and the Review lines for the reviewers.
1. `vkit run <lib>` from a clean state passes, and `vkit report` updated SUMMARY.md.
2. `vkit selftest` passes (and `vkit selftest --full` if you changed the engine).
3. The result JSON shows 0 sorries and no nonstandard axioms for every claimed theorem.
4. State `Functions N/M at full-correctness`. Anything below N/N, or any weaker label, is a
   candidate and the PR lists what is open (SUMMARY.md has the table).
5. Planted-bug check: at least 10 mutants (the reviewer picks them at review), each rejected.
6. `libraries/<lib>/NOTES.md` has: pinned version + commit, properties proved, exclusions
   and assumptions (std models, rewrites, bounds), how to re-run, time to re-run.
7. No build outputs committed (`.lake/`, `target/`, caches, tarballs).

## PR
- One library (or one engine change) per PR, adding or changing only `libraries/<lib>/` (plus
  notes). Title: `verify(<lib>): <N/M functions, what is proved>` or `engine: <change>`.
- Fill the PR template. Under "Evidence", paste the summary line from `latest.json`
  (proved/total, sorries, axioms) and the command you ran.
- Merging needs two sign-offs recorded in the PR: the maintainer, and a fresh adversarial review
  agent with no access to your notes. The author can be neither. AI-written proofs are welcome;
  a human owns the PR.
- If you found an upstream bug, link the draft issue text. Don't file upstream issues without
  the user's go-ahead.

## Claim wording
"verified: 43/43 functions at full-correctness (Lean, standard axioms only)", "candidate: 9/43 at full-correctness, rest open", "bounded: CBMC, lengths 0..32".
Never round partial work up.
