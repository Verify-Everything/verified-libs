# Worked examples in this repo

- `selftest/c-demo/sat.c`: smallest annotated file the gate proves (13/13 goals).
- Neovim base64 (see `notes/libraries/neovim.md`): decoder fully proved with exact
  counter invariants and bit-op lemmas checked by Z3; found a >2 GiB length bug that became an
  upstream issue.
- inih (see `notes/libraries/inih.md`): function-pointer prelude, `-wp-no-pruning`,
  `strlen` framing workarounds.

Lemma check with Z3 bit-vectors (Python):
```python
from z3 import BitVec, URem, prove
x = BitVec("x", 32)
prove((x & 4095) == URem(x, 4096))   # prints "proved"
```
