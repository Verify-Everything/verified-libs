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
| `decode_utf8_lossy` | `debug_assert!(ptr::eq(..))` vs dropped | lossy | proved with debug assertions off; **open with debug assertions on** (below) |

Also proved: `after_percent_sign` (the same in both trees), including that
`h as u8 * 0x10 + l as u8` cannot overflow, and that `initial_bytes.len() - bytes_iter.len() - 3`
cannot underflow in either `if_any`.

Planted bugs (each must make a proof fail): encoder `next` 7/7, `Display` 5/5, decoder `next`
5/5, `if_any` 6/6, `decode_utf8_lossy` 3/3. Total 26/26 rejected.

### decode_utf8_lossy with debug assertions on
With `debug-assertions` on, the original also evaluates
`core::ptr::eq(utf8.as_bytes() as *const [u8], &*bytes)` and panics if it is false. It is true
whenever `String::from_utf8_lossy` returns `Cow::Borrowed` of its own input, which std's code
does. Creusot 0.14 translates a reference-to-pointer cast as a *fresh* pointer
(`Opaque.fresh_ptr`, only the length is kept), so the two addresses are unrelated and this
assertion cannot be proved; the same crate with debug assertions on fails exactly at that goal
(checked). Closing it needs a tool with an address model for references (or a std contract about
pointer identity that this check does not add).

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
- Creusot 0.14.0 and its `creusot-std` specs, Why3 and the four SMT solvers.

## Not yet done
- The engine (`vpipe`) does not run this check, so CI does not re-check it and `functions.toml`
  still lists these functions as open. Running it from vpipe needs Creusot pinned in
  `toolchain/versions.toml` and the selftest (an engine PR, separate from this library).
- The derived `Debug` for `PercentDecode` (Aeneas emits `sorry`) is not covered here.
