# percent-encoding verification status

Thread: "Verify percent-encoding in Lean". Upstream: servo/rust-url @ 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (percent-encoding 2.3.2).
Stack: Aeneas nightly-2026.10.23-fdebf20, Rust nightly-2026-09-17, Lean 4.35.0, mathlib v4.35.0 (shared cache).

## Status (2026-10-24 05:15 UTC): DONE, all proved, standard axioms only
Bundle: `verification-notes/percent-encoding/` (README.md lists every theorem and every assumption).
Re-run: `cp -r verification-notes/percent-encoding /tmp/pe && cd /tmp/pe && bash pipeline/run.sh` -> PASS in ~1.5 min from a fresh copy (with the shared mathlib cache).

Proved on the Aeneas translation:
- Encoder output == reference spec for every input; never panics; every yielded chunk is ASCII (justifies `from_utf8_unchecked`).
- Output alphabet: all ASCII; only `%` and `0-9A-F` may be in the set.
- Decoder output == reference spec; never panics (no u8 overflow in `h*16+l`).
- Round trip decode(encode x) = x when the set contains `%`; holds for NON_ALPHANUMERIC; proved false for CONTROLS (`%41` -> `A`).
- CONTROLS / NON_ALPHANUMERIC contents; `AsciiSet::add` semantics; 768-byte `%XX` table correct.

Assumed: 2-hunk source patch (differentially tested, 18.8M cases), 10 hand-written std models in FunsExternal.lean, Aeneas faithfulness, 2 post-processing fixes.
Out of scope: Display/Debug impls, alloc feature (Cow, decode_utf8*).

Notable: `AsciiSet::add/remove` with a non-ASCII byte index out of bounds (panic / const-eval error). Not a bug in practice (docs say ASCII), but `add_spec` needs `b < 128`.

## Time spent
~25 min tooling (nix detour, then release tarball), ~35 min mathlib from source (before the shared cache existed), ~60 min proofs.

Adopted by vpipe (05:25 UTC): canonical proofs now in pipeline/proofs/percent-encoding/; run with `vpipe run percent-encoding` (49/49 proved, ~2.5 min). Edit proofs there.
