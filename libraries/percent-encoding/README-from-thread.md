# percent-encoding: formal verification in Lean (via Aeneas)

Crate: `percent-encoding` 2.3.2 from servo/rust-url @ 00a6ce58d02f (no_std core: encoder, decoder, AsciiSet).
Re-run everything: `bash pipeline/run.sh` (the shared folder is noexec, so call it through bash) (stages: setup fetch test extract prove report). Output: `build/report.md`.

## What is proved (all on the Aeneas translation of the Rust code, only Lean's 3 standard axioms)
| Theorem (`lean/Proofs/`) | Meaning |
|---|---|
| `percent_encode_correct` | Collecting `percent_encode(input, set)` never panics and equals the reference encoder `Spec.encode`. |
| `encode_next_spec` | Every chunk the iterator yields is ASCII, so the `unsafe from_utf8_unchecked` calls are sound. |
| `percent_encode_output_allowed` | Every output byte is ASCII; the only output bytes that are in the set are `%` and `0-9A-F`. |
| `percent_decode_correct` | Collecting `percent_decode(input)` never panics (no overflow in `h * 0x10 + l`) and equals `Spec.decode`. |
| `percent_roundtrip` | If the set contains `%`, decoding the encoder's output gives back the input. |
| `roundtrip_NON_ALPHANUMERIC` | Same, specialised to `NON_ALPHANUMERIC` (no side condition). |
| `CONTROLS_no_roundtrip` | With `CONTROLS` the round trip fails (`%41` -> `%41` -> `A`): the side condition is needed. |
| `CONTROLS_spec`, `NON_ALPHANUMERIC_spec` | The built-in sets contain exactly what the docs say. |
| `add_spec` | `AsciiSet::add` inserts exactly one ASCII byte. |
| `enc_table_slices` | The 768-byte `%XX` lookup table is right for all 256 bytes (kernel-checked). |

## What is assumed (the trusted base)
1. `rust/aeneas-friendly.patch`: two rewrites Aeneas needs (early return in a loop -> while loop; `Option::map` closure -> match).
   Checked by the upstream unit tests and an 18.8M-case differential test against unmodified upstream (`rust/difftest`), not proved.
2. `lean/PercentEncoding/FunsExternal.lean`: hand-written Lean models of 10 Rust std functions (`char::to_digit`, `u8::is_ascii`,
   `split_first`, `from_utf8_unchecked`, `size_of::<u32>`, `Option` `?`, ...). Five unused ones stay as `axiom`s; no main theorem uses them.
3. Aeneas/Charon translate Rust faithfully, and the Aeneas Lean library models of `core` are correct.
4. `pipeline/postprocess.py` fixes two gaps in the Aeneas Lean library (missing `U32.rem`, missing `Iterator.size_hint` field).
5. "Collect" is modelled by `encodeCollect`/`decodeCollect`, which call the translated `next` until `None`.

## Out of scope
`Display`/`Debug` impls (Aeneas cannot translate them; they appear as `sorry` in the generated code but no theorem uses them),
and the `alloc` feature (`Cow`/`String` conversions, `decode_utf8`, `decode_utf8_lossy`).

## Layout
- `pipeline/` run.sh, versions.env (all pins), postprocess.py, check_externals.py (fails if Aeneas asks for new std models), report.py
- `rust/` patch + differential test
- `lean/` Lean project; `PercentEncoding/{Types,Funs}.lean` are generated, `FunsExternal.lean` is hand-written, `Proofs/` is ours
