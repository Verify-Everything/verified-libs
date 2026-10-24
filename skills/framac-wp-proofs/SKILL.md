---
name: framac-wp-proofs
description: Prove C code correct with Frama-C WP and ACSL annotations (memory safety, no UB, functional contracts) in a vpipe C proof project. Use when verifying a C library with Frama-C, writing ACSL, or debugging unproved WP goals.
---

# Frama-C WP proofs

Project (made by `vkit new --lang c`): `libraries/<lib>/` with ACSL kept as a patch or
annotated copy of the pinned upstream file. `vkit run <lib>` applies, runs WP, records
proved/total per function in `results/<lib>/latest.json`.

## Every function
A C function counts as verified when all its WP goals are proved and it has an `ensures`
contract. Every function definition in the listed files counts, `static` helpers included;
the library is finished at Functions N/N.

## Forbidden (CI fails the entry)
`admit` clauses, unproved goals, runs without `-wp-rte`, unchecked `assumes`. Bit-op lemmas are
allowed only if proved separately (e.g. Z3 bit-vectors) with that proof in the repo. Each
function must reach `full-correctness`: a complete `ensures` contract, not just safety.

## Workflow
1. Start with CBMC (**cbmc-bounded-checks**) to find bugs fast; fix the spec, not the code.
2. Contracts first: `requires` (valid buffers, lengths), `assigns`, `ensures`. Then loop
   invariants, loop assigns, loop variants.
3. Run, read the per-function table, attack the function with the most unproved goals.
4. Honesty check: strip `/*@ */` and `//@` from the annotated file and diff against upstream;
   only annotations may differ (the engine runs this).

## Options that matter
- `-wp-rte` adds runtime-error goals (overflow, bounds, division). Always on.
- `-wp-literals` so WP knows string-literal contents (needed for `strchr(";#", c)`).
- `-wp-model Typed+Cast` when code casts `char*` to `uint8_t*`; state the link you need as a
  precondition and list it as an assumption. `Bytes` model is slower and proved less.
- `-wp-no-pruning` can be ~15x faster on big branchy functions (Qed's pruning pass).
- `-DNDEBUG` so `assert()` doesn't add goals.
- `-wp-session <dir> -wp-cache update` reuses prover results across runs.
- Provers: z3 + cvc5 (Alt-Ergo is unfree in nixpkgs; fine to add from opam).

## Pitfalls
- SMT can't do `&`, `<<`, `>>` on unbounded integers: add small ACSL lemmas
  (`(x & 4095) == x % 4096`, `(x << 6) == x * 64` for bounded x), use them via `assert`, and
  check the lemmas separately with Z3 bit-vectors (Python `z3-solver`).
- WP ignores fresh allocation (`\fresh`, `allocates`): an `assigns` clause on a buffer the
  function just malloc'd can't be proved. Drop it and say so.
- `p <= q` compares offsets only: add `\base_addr(p) == \base_addr(\at(p, Pre))` to invariants.
- Logic functions like `strlen` aren't framed after writes: state facts at `Pre` or per cell.
- `char a[50] = "";` gives WP only `a[0] == 0`.
- Function pointers: redirect calls with an `-include` prelude macro to an abstract function
  with a contract covering every implementation.
- Debug a stuck goal: `-wp-prover none -wp-print > goals.txt` shows what Qed simplified away.
- Exact-counter invariants (`out_i * 8 + acc_len == 6 * src_i`) plus a few case-split asserts
  close most buffer-bound goals.

Details and examples: [references/examples.md](references/examples.md).
