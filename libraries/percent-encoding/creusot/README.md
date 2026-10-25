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
   `#[variant]` and single-statement ghost `snapshot!`/`proof_assert!` lines may differ),
2. checks the SHA-256 of `creusot-std-0.14.0.crate` and applies `creusot-std-fmt.patch`,
3. translates both crates and proves every Why3 file with why3find (alt-ergo, z3, cvc5, cvc4).

## Status (2026-10-25)

| Upstream function | Original vs patched | Crate | Result |
|---|---|---|---|
| `Iterator for PercentEncode::next` | `for … enumerate()` with early `return` vs `next_chunk` `while` loop | encode | proved, same spec `chunk_ok`/`step` |
| `fmt::Display for PercentEncode::fmt` | `for c in (*self).clone() { formatter.write_str(c)? }` vs `write_chunks` | encode | proved, same spec `display_ok` |
| `Iterator for PercentDecode::next` | `Option::map` with a closure vs `match` | decode | proved, same spec `dstep` |
| `PercentDecode::if_any` | `while bytes_iter.any(..)` with early `return` vs `decode_if_any` | – | open |
| `decode_utf8_lossy` | `debug_assert!(ptr::eq(..))` removed by the patch | – | open |

`after_percent_sign` (the same in both trees) is proved in the decode crate, including that
`h as u8 * 0x10 + l as u8` cannot overflow. Planted bugs: 7 in the encoder `next` pair and 5 in
the decoder; each one made a proof fail. (The Display mutants are being run.)

## What "agree" means
Same return value and same final state of `self`, where slices and slice iterators are compared
by their contents (Creusot's view), not by address. For `Display`, both versions make the same
sequence of `write_str` calls with the same strings, and return the same result, for any sink
whose response to a write depends only on its state and the string (`sink_after`/`sink_ok`).

## Trusted base added by this check
- **T1** (UTF-8): every byte `b < 128` is a char with code point `b` whose UTF-8 encoding is `[b]`.
- **T2** std contracts written here, as documented: `str::from_utf8_unchecked` (requires valid
  UTF-8; the result's bytes are the input), `<[T]>::split_first`, `u8::is_ascii`, indexing
  `[T; N]` (forwards to the slice impl), `fmt::Write::write_str` (sink model),
  `Clone for slice::Iter`, `From<u8> for char` (code point = byte), `char::to_digit` (a digit
  is below the radix).
- **T3** purity: `AsciiSet::contains` and `percent_encode_byte` are used as opaque deterministic
  functions of their arguments (both are fully specified in Lean: `contains_spec`,
  `percent_encode_byte_spec`). Equivalence does not depend on what they compute.
- **T4** `creusot-std-fmt.patch`: gives `Formatter::write_str` the same contract as
  `<Formatter as fmt::Write>::write_str` (in core both are `self.buf.write_str(data)`).
  creusot-std 0.14.0 ships `Formatter::write_str` with no contract at all.
- Creusot 0.14.0 and its `creusot-std` specs, Why3 and the four SMT solvers.
