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

## 2026-10-24 08:40-09:30 UTC: second tool (Yerin chose it at 08:37)
- Tool: Creusot v0.14.0 (2026-10-12, Rust nightly-2026-08-03). Built from source fine (`cargo build --release -p cargo-creusot -p creusot-rustc`, ~4 min).
- Blocked: Creusot pins Why3 git-05bf4ddf and why3find git-0f054b93; their sources are only on gitlab.inria.fr / git.frama-c.com / opam.ocaml.org, all denied by this sandbox's network policy. nixpkgs Why3 1.8.2 is too old: it rejects Creusot 0.14's Coma (`fun (_x: T) -> ...` lambdas), and why3find master needs newer Why3 APIs. Asked Yerin to allow those three hosts (new cloud environment; only new sessions pick it up).
- Got working without them: solvers at Creusot's pinned versions (Alt-Ergo 2.6.4 and CVC5 1.4.1 from GitHub releases, sha256 checked; Z3 5.1.0 from nixpkgs; CVC4 1.8 via installer), why3find 1.3.0 built from the github.com/creusot-rs/why3find mirror (tag 1.3.0).
- Creusot on the unmodified crate needs ghost-only additions: `extern crate creusot_std` under cfg(creusot), DeepModel for the PartialEq types, IteratorSpec for both Iterator impls, and visibility fixes for the consts. Plan: annotated copy whose non-ghost tokens equal upstream (pipeline check strips #[cfg(creusot)] items and creusot attributes, then diffs).
- Disk: `nix-collect-garbage` freed 15 GB (old Nix detour). Don't write through a symlink when wrapping a tool (I overwrote the why3find binary once).

## 2026-10-24 11:30 UTC: Creusot proofs on the unmodified code ("Finish percent-encoding with Creusot" thread)
Bundle: verification-notes/percent-encoding-creusot/bundle/ (README.md has the full table, trusted base and run steps; `./run.sh`).
- Proved with Creusot v0.14.0 on byte-identical upstream code (ghost-only check passes), against specs that mirror Proofs/Spec.lean: PercentEncode::next, Display::fmt (exact sink output), PercentDecode::next (closure capturing &mut), PercentDecode::if_any, derived Debug for PercentDecode (no panic), plus after_percent_sign, contains, should_percent_encode.
- decode_utf8_lossy (private): functional spec proved, but the `debug_assert!(core::ptr::eq(raw_utf8, &*bytes))` goal is NOT proved. Creusot models `&x as *const T` as a fresh pointer, so no contract can prove ptr::eq of two reference-derived pointers. Still open: blocks completion.
- Trusted std contracts are difftested by bundle/spectest (1.58M checks). percent_encode_byte is trusted in Creusot with Lean's proved contract.
- functions.toml not changed yet: vpipe only knows Lean theorems; the pipeline thread was asked to add a Creusot evidence type before the 4 entries drop `status = "open"`.
Open now: decode_utf8_lossy's debug_assert; gates 5, 6, 9, 10 (people/infra).

## 2026-11-02 MIR-level audit (Charon match-guard bug)
Re-extracted the patched crate with stock Charon 0.1.293 at default MIR and with `--mir elaborated`, then diffed.
Every function body is identical. The only difference: elaborated leaves out the unused trait-instance definitions
for Borrow<[T]> for Vec, Borrow<str> for String and their ToOwned impls (plus their template axioms). The default
extraction equals the pipeline's Funs.lean apart from postprocess edits. Funs.lean has no `fail .panic` and the crate
has no dependencies, so the parking_lot/third-party interior-mutability issue does not apply. No theorem is affected.

## 2026-11-02: decode_utf8_lossy's debug_assert proved with Kani ("Finish percent-encoding with Creusot" thread)
Details: verification-notes/percent-encoding-creusot/bundle/kani/README.md.
- Kani 0.68 on the real decode_utf8_lossy (pinned commit), Owned non-empty input of any length up to 2^40 bytes, with String::from_utf8_lossy replaced by a byte-for-byte copy of std's source (generated by script; one loop invariant added). SUCCESSFUL. The std fact alone (Borrowed result = input slice) also SUCCESSFUL; a must-fail control fails. Same std code in nightly-2026-08-03, nightly-2026-08-21 and 1.97.0.
- Edge case: Cow::Owned(empty Vec) trips the assert in Kani's model (address of "" vs the Vec's dangling pointer; Rust does not promise they match, rustc today makes both 0x1). Unreachable from the public API. Creusot now carries "Owned input is non-empty" as a precondition and proves From<PercentDecode> for Cow<[u8]> and PercentDecode::decode_utf8_lossy meet it (Creusot suite: 18/19 entries, the 19th is the ptr::eq goal Kani covers).
- Note: crates.io 2.3.2 differs from the pinned commit 00a6ce58 in two lines (`self.clone().into()` vs `self.into()` in decode_utf8 and decode_utf8_lossy). Proofs are on the pinned commit.
- Labels: the ptr::eq part is "Kani, ≤2^40 bytes, std via verified copy". Whether that meets the strict standard is Yerin's call.
- 2026-11-02 03:17 UTC: Yerin decided the Kani proof counts as verified, labelled clearly (Kani 0.68, inputs ≤ 2^40 bytes, std from_utf8_lossy via generated byte-for-byte copy). percent-encoding is finished once the full vpipe run passes.
