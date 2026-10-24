# Trust model: what "proved" means here

A result is only as good as (1) the spec, (2) the checker, and (3) the assumptions in between.

## What you trust
- **The spec.** Lean `Spec.lean` or ACSL contracts state what "correct" means. Read them; a
  proof of the wrong statement is worthless. Specs are written independently of the code.
- **The checkers.** Lean's kernel; Frama-C WP with Why3, Z3, CVC5; CBMC with its SAT solver.
- **Translation.** Charon + Aeneas translate Rust MIR into Lean; we trust that translation
  matches Rust semantics. Frama-C trusts its C front end and memory model.
- **Std models.** Rust std functions Aeneas cannot translate are modelled in
  `External/FunsExternal.lean`. Each one used by a theorem is an assumption and is listed.
- **Pins.** Results hold for the pinned upstream commit and pinned tool versions only.

## What the pipeline checks for you
- Lean: after a passing build, every hand-written theorem's axioms are collected. Only
  `propext`, `Classical.choice`, `Quot.sound` count as proved. `sorryAx`, std-model `axiom`s,
  and `_native` axioms (from `native_decide`/`bv_decide`) mark the theorem as not proved.
- C: annotation-only check (the annotated file minus ACSL must equal upstream).
- Both: results record tool versions, the upstream commit, and the engine version.

## When a library is finished
Only when every function in the pinned upstream source is verified or has a verified fix. The
engine scans the upstream source itself (not the patched copy or a model crate), counts trait
impls and code behind `cfg` for other targets, and reports `Functions N/M`. Bounded checks and
tests do not make a function verified.

## Strength of claims
Labels used in every CLAIM.md (defined in [STANDARDS.md](../STANDARDS.md)):
`full-correctness`, `safety-contracts`, `no-ub`, `bounded`, `tested`. Only `full-correctness`
admits; an entry takes its weakest function's label, and anything below goes under `candidates/`.
A function still unverified is `open` and listed in results/SUMMARY.md.

## Mutation checks
A proof can be vacuous (a precondition that is never true, a harness that never runs). Every
library records planted bugs and whether the checks caught them.
