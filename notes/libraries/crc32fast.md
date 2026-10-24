# crc32fast verification status

Thread: "Verify crc32fast in Lean". Upstream: github.com/srijs/rust-crc32fast @ d2363eab95ebc85fcf726d1c8fa845148e474591 (v1.5.3).
Tools: Aeneas nightly-2026.10.23-fdebf20 (Charon 0.1.293), Rust nightly-2026-09-17, Lean 4.35.0, mathlib v4.35.0.

## Status (2026-10-24): done for the portable code
All goals proved, no `sorry`. Every headline theorem depends only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`). No `bv_decide` or `native_decide`.

## What is proved
The spec (`Spec.lean`) is the textbook bit-at-a-time reflected CRC-32: poly 0xEDB88320,
init and final XOR 0xFFFFFFFF, no tables. Check values proved: "123456789" = 0xCBF43926,
"" = 0, "hello world" = 0x0D4A1185. `update prev data` continues a finished CRC.

| Theorem | Statement (informal) |
|---|---|
| `update_slow_eq` | byte-at-a-time table loop = spec `update` |
| `update_fast_16_eq` | slice-by-16 loop (with the slow tail) = spec `update` |
| `table_eq` | all 4,096 entries of CRC32_TABLE = the spec's table |
| `hash_eq` | `crc32fast::hash buf` = `crc32 buf` |
| `update_eq` | `Hasher::update` = spec `update`, byte count advanced |
| `update_update_eq_hash` | new, update a, update b, finalize = `hash (a ++ b)` |
| `Crc32Spec.update_append` | spec: incremental = single pass |
| `combine_eq` | `combine::combine c1 c2 len2` = CRC of the concatenation (GF(2) math) |
| `hasher_combine_eq`, `combine_eq_hash` | `Hasher::combine` of two hashers = hash of a ++ b |

## Assumptions and limits
- Only the portable path. SIMD (pclmulqdq, aarch64) is not extracted: Charon runs for a
  riscv64 no_std target, where the crate's cfg makes the SIMD state an empty enum.
- `Hasher::update` assumes the u64 byte counter does not overflow (Aeneas turns overflow into
  a panic). The CRC result itself has no such limit.
- Std functions Aeneas cannot see are hand-modelled in `Crc32fast/External/` (wrapping_neg,
  unwrap_or_else, Option::clone, `?` branch/from_residual), following the Rust docs. The two
  `fmt` (Debug) items stay axioms; no proved theorem uses them.
- Trusted: Lean kernel, Aeneas's translation of Rust semantics, Charon.

## Where things are
- Pipeline copy (re-runnable): `pipeline/libraries/crc32fast.toml`, `pipeline/proofs/crc32fast/`.
  Re-run: `python3 /mnt/project-files/pipeline/bin/vpipe.py run crc32fast`. Results in
  `pipeline/results/crc32fast/latest.json`.
- `proofs/crc32fast/Cargo.lock` is the reviewed lockfile; vpipe (v0.1.2+) runs Charon with `--locked`.
- Lean build of the proofs: ~2 min after the mathlib cache restore; `Table.lean` ~6 s.

## Re-verify a new release
Bump `commit`/`version` in the manifest and run. Things most likely to break: the extracted
function names (loop bodies are named `..._loop`, `..._loop0`), the External models if
Aeneas's template changes, and the table proof if the table layout changes.
