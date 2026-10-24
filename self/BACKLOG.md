# Pipeline backlog

The improve loop reads this list, works the top unblocked item, and moves it to Done with a
CHANGELOG entry. Humans and threads may add items. Newest evidence wins.

## Open
- [ ] Lean: generate a `Spec.lean` stub per extracted public function (signature + `sorry` theorem) so the agent starts from a full list of obligations.
- [ ] Collect common failure signatures from results/*/ logs into templates/prompts so the agent sees known fixes first.
- [ ] `vpipe new --agent`: let an agent fill the manifest (extract args, scope, exclusions) from the upstream repo.
- [ ] CBMC stage for C: bounded checks as a quick first pass before Frama-C WP (Neovim thread: 75 harnesses in 16 s, found an over-2 GiB bug). Needs a cbmc setup script (GitHub .deb works).
- [ ] Mutation check: plant known bugs and confirm proofs/harnesses fail (Neovim's mutants.sh); flags vacuous proofs and stale harnesses after an upstream bump.
- [ ] Frama-C: document `-wp-no-let` (200x on inih's main loop), `-wp-model Typed+Cast`, `-DNDEBUG` and the `-include` prelude for function pointers in the C prompt; add a z3 bit-vector lemma-check step (Neovim's check_lemmas.py).
- [ ] Frama-C via Docker image (inih uses Frama-C 32.1 + Alt-Ergo in Docker; Nix gives 33 without Alt-Ergo): pick one, so C results are comparable.
- [ ] Model-crate pattern is now used by semver and Helix: add a `vpipe new --model` scaffold (model crate + differential test skeleton wired into [test]).
- [x] Adopt finished thread work: crc32fast, percent-encoding, semver run natively (2026-10-24).

## Open (new)
- [ ] Audit only sees `axiom`s; defs used as trusted std models in FunsExternal.lean (general.md: `from_utf8_unchecked := ok`) are invisible to it. List defs from FunsExternal.lean in the result as assumptions.

## Done
- [x] Frama-C per-function proved/total in results and SUMMARY.md (first change made by `vpipe improve` in a test copy, 2026-10-24; kept by the gate, ported here).
- [x] Mathlib cache restore verified end to end: Lean fixture restores the shared tarball and builds in about 45 s (2026-10-24).
- [x] Lean axiom audit: after a passing `lake build`, every hand-written theorem is checked with `Lean.collectAxioms`; only propext/Classical.choice/Quot.sound count as proved, extras are recorded per theorem and counted in SUMMARY.md (2026-10-24T04:33:24Z).
- [x] Axiom audit verified with the full gate and a negative test (2026-10-24).
- [x] Cargo.lock pinning, External template diffing, bv_decide guidance (from crc32fast adoption, v0.1.2).
- [x] Patch files, [test] commands (upstream + differential tests), postprocess hooks, strict externals (percent-encoding adoption, v0.1.3).
- [x] Frama-C -wp-literals default, WP session cache, annotation-only honesty check (v0.1.4).
