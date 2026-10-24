---
name: cbmc-bounded-checks
description: Write CBMC harnesses for C functions (bounded model checking for memory safety, overflow and functional properties) plus a mutation check that proves the harnesses are not vacuous. Use as the quick first pass on any C library before Frama-C WP, or when hunting bugs in C parsing/encoding code.
---

# CBMC bounded checks

## Harness pattern
```c
#include "spec.h"           // reference model, written byte by byte, no tricks
void harness(void) {
  size_t n; __CPROVER_assume(n == LEN);      // one exact length per run
  unsigned char *in = malloc(n); __CPROVER_assume(in != NULL);
  // nondet contents: malloc'd memory is already nondet in CBMC
  char *out = encode(in, n);
  __CPROVER_assert(equals_model(out, in, n), "matches reference");
  free(out); free(in);       // free everything, or --memory-leak-check fails on the harness
}
```
Run: `cbmc harness.c upstream.c -I stubs -DLEN=$n --function harness --bounds-check
--pointer-check --signed-overflow-check --unsigned-overflow-check --memory-leak-check
--unwind $((n+2)) --unwinding-assertions`.

## Lessons
- Exact lengths (`n == LEN`, loop LEN over 0..32, 4 in parallel), not `n <= MAX`: a symbolic
  length up to 5 ran out of 15 GB; exact lengths finish in seconds.
- Compile the upstream .c unmodified; stub its internal headers in `-I stubs`.
- `--conversion-check` flags `(char)int_in_128..255`, which is implementation-defined, not UB.
  Leave it off or expect noise.
- Bounded is not a proof for all lengths. Label it `bounded` and report "checked for lengths
  0..N". Bounded results go under `candidates/` only; every function still needs an unbounded
  proof (Frama-C WP) at full-correctness before the entry can be called verified.
- Always pass `--unwinding-assertions` (the template does); a run without it is forbidden.

## Mutation check (always)
Plant 10+ known bugs with `sed` on a copy (off-by-one bound, wrong table entry, flipped
comparison, dropped padding), run the harnesses, and confirm each mutant fails at least one.
A mutant that survives means a harness is vacuous or too weak. Re-run after upstream bumps:
it also shows when a harness went stale. Record results in the result notes.

Templates (copy into `libraries/<lib>/cbmc/`): [templates/](templates/): `harness.c`, `run_cbmc.sh`, `check_lengths.sh`, `mutants.sh`. The Neovim base64 work (`notes/libraries/neovim.md`) is a finished example.
