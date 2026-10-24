# Known Aeneas/Lean library gaps (release nightly-2026.10.23-fdebf20)

Fixed after each extraction by a manifest `postprocess` hook (see libraries/percent-encoding/scripts/postprocess.py):
- Generated code calls `U32.rem` (from a const `<<`), which does not exist: replace with `a % b`.
- Generated `Iterator` instances set `size_hint := ...`; the library structure has no such field: delete it.
- Array literal of 768 elements hits `maxRecDepth`: pass `-max-recdepth 16384` in `aeneas_args`.
- `UScalar.wrapping_shl` is not `@[expose]`: from a `module` file it can't be evaluated. Put
  those proofs in a plain (non-`module`) file.

Std models in FunsExternal.lean
- `Str` is `Slice U8`; `from_utf8_unchecked := ok` is a fine model. Use a helper
  `strBytes (s : Str) := bytes s` to avoid Str/Slice mismatches in simp.
- Keep generic signatures but make proofs easy: `size_of (T) := if T = U32 then ok 4 else fail .panic`.
- When Aeneas is upgraded, the engine writes `External/*.new` if the expected models changed;
  diff and update the hand-written file first.

Setup pitfalls
- Lean version must equal `backends/lean/lean-toolchain` of the Aeneas release (setup checks).
- Charon needs the exact Rust nightly in the release's `rust-toolchain` (setup reads it).
- Mathlib from source takes hours; `vkit setup mathlib` fetches the prebuilt cache once and the
  engine restores it into every project.
