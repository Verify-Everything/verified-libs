// Harness template. Copy, rename to <function>_harness.c, fill the TODOs.
// The reference model (spec.h) should be the simplest correct code you can write:
// byte by byte, no tables, no tricks. It is the spec, so review it carefully.
#include <stdlib.h>
#include <string.h>
#include "spec.h"          // TODO: reference model, e.g. size_t model_encode(...)

#ifndef EXACT_LEN
#define EXACT_LEN 4
#endif

void harness(void) {
  size_t n = EXACT_LEN;                       // one exact length per run (fast)
  unsigned char *in = malloc(n ? n : 1);
  __CPROVER_assume(in != NULL);               // contents are nondet: all inputs of length n
  // TODO: call the upstream function under test
  // char *out = upstream_encode(in, n);
  // TODO: assert the property
  // __CPROVER_assert(out != NULL && model_matches(out, in, n), "matches reference model");
  // free(out);
  free(in);                                   // free everything (memory-leak-check)
}
