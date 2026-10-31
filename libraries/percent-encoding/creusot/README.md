# Creusot: the patched bodies equal the original code (admission gate 1)

The Lean proofs in `../Proofs/` cover the code Aeneas extracts from the crate *after*
`../rust/aeneas-friendly.patch`. Aeneas cannot read the original bodies of five functions
(early return in a loop, a closure capturing `&mut`, a `for … ?` over a clone, `any` with a
closure, a raw-pointer `debug_assert!`). Here Creusot 0.14.0 reads the **original upstream
bodies** and the **patched bodies**, and proves that each pair meets one exact specification, so
the two agree on every input. Lean's result on the patched body then holds for the original.

Run: `bash creusot/run.sh <upstream percent_encoding dir> <patched percent_encoding dir>`
(vpipe makes both under `$VPIPE_WORK/percent-encoding/{src,patched}`). It
1. checks with `check_verbatim.py` that every body marked `// verbatim:` equals the pinned
   upstream (or patched) source once proof annotations are removed (only `#[invariant]`,
   `#[variant]` and single-statement ghost `snapshot!`/`proof_assert!` lines may differ; code
   after a ghost statement or attribute on the same line is rejected),
2. checks the SHA-256 of `creusot-std-0.14.0.crate` and applies `creusot-std-fmt.patch`,
3. translates the three crates and proves every Why3 file with why3find (alt-ergo, z3, cvc5,
   cvc4), one file at a time with a wall-clock cap.

Every loop has a `#[variant]`, so these are total-correctness proofs (without a variant Creusot
proves partial correctness only; a wrong variant is rejected, checked).

## Status (2026-10-25)

| Upstream function | Original vs patched | Crate | Result |
|---|---|---|---|
| `Iterator for PercentEncode::next` | `for … enumerate()` with early `return` vs `next_chunk` `while` loop | encode | proved, spec `chunk_ok`/`step` |
| `fmt::Display for PercentEncode::fmt` | `for c in (*self).clone() { formatter.write_str(c)? }` vs `write_chunks` | encode | proved, spec `display_ok` |
| `Iterator for PercentDecode::next` | `Option::map` with a closure capturing `&mut self.bytes` vs `match` | decode | proved, spec `dstep` |
| `PercentDecode::if_any` | `while bytes_iter.any(..)` with early `return` vs `decode_if_any` (+ `decode_from_percent`, `position_of_percent`) | decode | proved, spec `if_any_ok` |
| `decode_utf8_lossy` | `debug_assert!(ptr::eq(..))` vs dropped | lossy | proved with debug assertions off; with them on, **assumed** under A-lossy-ptr for every input the only caller passes, by the written argument below (not checked by Creusot) |

Also proved: `after_percent_sign` (the same in both trees), including that
`h as u8 * 0x10 + l as u8` cannot overflow, and that `initial_bytes.len() - bytes_iter.len() - 3`
cannot underflow in either `if_any`.

Planted bugs (each must make a proof fail): encoder `next` 7/7, `Display` 5/5, decoder `next`
5/5, `if_any` 6/6, `decode_utf8_lossy` 3/3. Total 26/26 rejected.

### decode_utf8_lossy with debug assertions on
With `debug-assertions` on, the original also evaluates
`core::ptr::eq(utf8.as_bytes() as *const [u8], &*bytes)` and panics if it is false. Creusot
0.14.0 cannot prove this assertion, and no contract can fix that: the two casts
(`&[u8] as *const [u8]`) are in the original body itself, not in a std call, and Creusot
translates every reference-to-pointer cast as `Opaque.fresh_ptr`, i.e. `any` with
postcondition `true`, keeping only the slice length (`creusot/src/backend/program.rs`,
`RValue::Ptr`; `prelude.coma`, `module Opaque`). The two addresses are therefore unrelated
in Creusot, whatever `from_utf8_lossy`, `as_bytes` or `ptr::eq` promise. The same crate with
debug assertions on fails exactly at that goal (checked 2026-10-25).

So the debug case is covered by the named assumption **A-lossy-ptr** (T5 below, maintainer
decision 2026-10-31) and this argument, which is written here, **not machine-checked**:
1. The debug-only lines have no effect besides the possible panic: `str::as_bytes` and
   `ptr::eq` only read, and `raw_utf8` is not used again. So if the assertion holds, the
   debug-on original behaves as the debug-off original, which Creusot proves equal to the
   patched body.
2. The assertion holds when `bytes` is non-empty: `from_utf8_lossy(&bytes)` returned
   `Cow::Borrowed(utf8)`, so by A-lossy-ptr `utf8` has the address and length of `&*bytes`
   (both derefs of the same unchanged `Vec`, so the same buffer); `str::as_bytes` keeps
   address and length; `ptr::eq` on `*const [u8]` compares both (T2).
3. `bytes` is never empty here. The only caller is `PercentDecode::decode_utf8_lossy`
   (upstream `src/lib.rs:330`), which passes `self.into()`; `From<PercentDecode> for Cow<[u8]>`
   (`src/lib.rs:281`) gives `Cow::Owned(vec)` only for `if_any() == Some(vec)`, and
   `if_any_ok` (proved for the original `if_any` in `decode/`) gives
   `vec.len() == i + 1 + dcount(rest) >= 1`.

**Empty input is a real exception, so the assumption is stated for non-empty input only.** For
an empty input std returns `Cow::Borrowed("")`, a static string, not a view of the input. Run
2026-10-31 on rustc 1.97.0: `from_utf8_lossy` of an empty `Vec::with_capacity(16)` borrows at
`0x1` while the Vec's buffer is elsewhere, so `ptr::eq` is false; the verbatim upstream
`decode_utf8_lossy(Cow::Owned(Vec::with_capacity(16)))` panics on this assertion in a debug
build and returns `""` in release. (`Vec::new()` happens to pass: its dangling pointer is also
`0x1`.) So with debug assertions on, the original and patched private function differ on that
input. They agree on every input the crate can pass (point 3). Gate 1 holds for this function
only in that sense: in its calling context, under A-lossy-ptr.

## What "agree" means
Same return value and same final state of `self`, where slices, slice iterators, `Vec`s,
`String`s and `Cow`s are compared by their contents (Creusot's view), not by address. For
`Display`, both versions make the same sequence of `write_str` calls with the same strings, and
return the same result, for any sink whose response to a write depends only on its state and the
string (`sink_after`/`sink_ok`).

## Trusted base added by this check
- **T1** (UTF-8): every byte `b < 128` is a char with code point `b` whose UTF-8 encoding is `[b]`.
- **T2** std contracts written here, as documented: `str::from_utf8_unchecked` (requires valid
  UTF-8; the result's bytes are the input), `<[T]>::split_first`, `u8::is_ascii`, indexing
  `[T; N]` (forwards to the slice impl), `fmt::Write::write_str` (sink model),
  `Clone for slice::Iter`, `From<u8> for char` (code point = byte), `char::to_digit` (a digit
  is below the radix), `ToOwned for [T]` (element-wise clone, as creusot-std's `to_vec`),
  `<slice::Iter as Iterator>::any` (consumes items up to and including the first one where the
  closure returns true; stated for closures whose state a call leaves unchanged), `str::as_bytes`,
  `ptr::eq` (address equality; only reached with debug assertions on),
  `String::from_utf8_lossy` (a deterministic function of the input bytes, seen through owned/text;
  when it returns `Borrowed`, the text's bytes are the input).
- **T3** purity: `AsciiSet::contains` and `percent_encode_byte` are used as opaque deterministic
  functions of their arguments (both are fully specified in Lean: `contains_spec`,
  `percent_encode_byte_spec`). Equivalence does not depend on what they compute.
- **T4** `creusot-std-fmt.patch`: gives `Formatter::write_str` the same contract as
  `<Formatter as fmt::Write>::write_str` (in core both are `self.buf.write_str(data)`).
  creusot-std 0.14.0 ships `Formatter::write_str` with no contract at all.
- **T5 A-lossy-ptr** (named assumption, maintainer decision 2026-10-31; narrowed to non-empty
  input, see above): when `v` is non-empty valid UTF-8, std's `String::from_utf8_lossy(v)`
  returns `Cow::Borrowed(s)` with `s` at `v`'s own address and length. Used only for
  `decode_utf8_lossy` with debug assertions on, through the written argument above, not as a
  Creusot contract. Tested, not proved: `rust/modeltest` checks it against real std on every
  non-empty valid input it generates (all inputs of 1–2 bytes, all 3–4 byte inputs over 25
  UTF-8 edge bytes, and 200,000 random inputs of up to 16 bytes; 38,654 valid ones on
  2026-10-31), on a slice and on a `Vec` buffer, and exits 1 if it fails.
- Creusot 0.14.0 and its `creusot-std` specs, Why3 and the four SMT solvers.

## Not yet done
- The engine (`vpipe`) does not run this check, so CI does not re-check it and `functions.toml`
  still lists these functions as open. Running it from vpipe needs Creusot pinned in
  `toolchain/versions.toml` and the selftest (an engine PR, separate from this library).
- The derived `Debug` for `PercentDecode` (Aeneas emits `sorry`) is not covered here.
- `decode_utf8_lossy` with debug assertions on rests on A-lossy-ptr and a hand-written
  argument. A tool with an address model for references could check points 1–3 by machine.
