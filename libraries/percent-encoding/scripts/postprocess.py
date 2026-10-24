#!/usr/bin/env python3
"""Small, logged fixes to Aeneas output for gaps in the Aeneas Lean library
(release nightly-2026.10.23-fdebf20). Each fix is semantics-preserving.

1. `U32.rem a b` (from Rust's const `<<` lowering) is not defined in the
   library; replace with the library's checked `%` (identical when b != 0,
   and b is the literal 32 here).
2. The library's `Iterator` structure has no `size_hint` field, so the
   generated trait instances fail. Drop that field from the instances; we
   never reason through the trait instance.
3. Inside `def PercentDecode.decode_utf8_lossy`, the call to the free function
   `decode_utf8_lossy` resolves to the method itself (Lean name lookup in the
   `PercentDecode` namespace). Qualify it as `percent_encoding.decode_utf8_lossy`.
"""
import re, sys, pathlib
p = pathlib.Path(sys.argv[1]) / "Funs.lean"
s = p.read_text()
n_rem = len(re.findall(r'\bU32\.rem ', s))
s = re.sub(r'\bU32\.rem (\S+) (\S+)', r'\1 % \2', s)
pat = re.compile(r'\n  size_hint :=\s+[^\n]+\n')
n_sh = len(pat.findall(s))
s = pat.sub('\n', s)
pat3 = re.compile(r'(def PercentDecode\.decode_utf8_lossy\b.*?\n  )decode_utf8_lossy ', re.S)
n_q = len(pat3.findall(s))
s = pat3.sub(r'\1percent_encoding.decode_utf8_lossy ', s)
p.write_text(s)
print(f"postprocess: replaced {n_rem} U32.rem, removed {n_sh} size_hint fields, qualified {n_q} decode_utf8_lossy call")
