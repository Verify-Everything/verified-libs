# percent-encoding verification status

Thread: "Verify percent-encoding in Lean". Upstream: servo/rust-url @ 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (percent-encoding 2.3.2).
Stack: Aeneas nightly-2026.10.23-fdebf20, Rust nightly-2026-09-17, Lean 4.35.0, mathlib v4.35.0 (shared cache).
Canonical copy: pipeline/libraries/percent-encoding/ (vpipe.toml, functions.toml, Proofs/, external/, tests/, rust/). Run: `vpipe run percent-encoding`.

## Status (2026-10-24 07:45 UTC): NOT finished. 21/26 functions verified on byte-identical upstream code; 5 open + derived Debug
Under the verified-libs admission standards (approved by Yerin 2026-10-24) the entry is a candidate.

Done:
- Default features (std, alloc) extracted and proved; 123/123 theorems, kernel replay (leanchecker) passes, only propext/Classical.choice/Quot.sound.
- Every function: encoder, decoder, AsciiSet ops (+ add/remove panic for bytes >= 128, proved), size_hint (both), Clone/PartialEq/Eq, Debug for AsciiSet and PercentEncode, Cow<str>/Cow<[u8]> From impls (incl. Borrowed vs Owned), if_any, decode_utf8, decode_utf8_lossy (method and private fn), Display (via write_chunks, exact output for any sink), _static_assert.
- No axioms and no `opaque` left in the std models. from_utf8_lossy is a real definition; from_utf8_unchecked (str and String) models fail on invalid UTF-8, so no-UB is proved.
- Std models differential-tested vs real std: tests/ModelTest.lean + rust/modeltest, 744k vectors (every UTF-8 input up to 2 bytes, edge-byte 3/4-byte inputs, 200k random), 0 mismatches.
- Translation cross-check: tests/CrossCheck.lean evaluates the extracted Lean code against the compiled UNPATCHED upstream crate (rust/crosscheck). Full run: 100k inputs (50k encode + 50k decode, 7 sets), 0 mismatches. vpipe runs 10k per run.

Open (each blocks admission):
1. Gate 1: 5 functions are proved only on the Aeneas-friendly patch (PercentEncode::next, Display::fmt, PercentDecode::next, if_any, private decode_utf8_lossy). Aeneas cannot translate the originals (nested &mut borrows through Enumerate/Iter, closure capturing &mut, early return in loop; tried --monomorphize, --monomorphize-mut, -loops-to-rec: no help). Needs a second tool on the real code (asked Yerin: Creusot/Verus recommended) or Aeneas support.
2. Derived Debug for PercentDecode: Aeneas emits `sorry` (cannot coerce &slice::Iter to &dyn Debug). Same second-tool question.
3. Gates 5, 6, 9, 10 need people/infra: spec review by Yerin, planted bugs chosen by an adversarial reviewer, container digest, two sign-offs.

Findings to report upstream (ask Yerin first): `AsciiSet::add`/`remove` panic (index out of bounds) on non-ASCII bytes; undocumented.

Disk: the session allowance is ~39 GB; Verus (unpacked ~1.5 GB + its Rust toolchain) did not fit alongside the rest. Free space first.
