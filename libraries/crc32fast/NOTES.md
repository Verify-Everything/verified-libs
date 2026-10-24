# crc32fast proof notes

Status and results: /mnt/project-files/verification-notes/crc32fast.md

Hand-written files (module `Crc32fast`):
- `Spec.lean`: the reference CRC-32 (bit at a time, no tables) and its check values.
- `Bits.lean`: kernel-checked bit helpers (`bv_bits` tactic). No `bv_decide` anywhere.
- `SpecLemmas.lean`, `CombineSpec.lean`: math about the spec (linearity, slice-by-16, x2n table).
- `Table.lean`: the 16 x 256 table equals the spec table (`decide +kernel`, ~6 s).
- `Baseline.lean`, `Hasher.lean`, `Combine.lean`: the Rust functions equal the spec.
- `External/`: hand-written models of the std functions Aeneas leaves as axioms
  (wrapping_neg, unwrap_or_else, Option::clone, `?` branch/from_residual). Only the two
  `fmt` axioms (Debug printing) stay; no proved theorem uses them.

Generated, never edit: `Crc32fast/Extracted/` (re-created on every run).

Headline theorems: `update_slow_eq`, `update_fast_16_eq`, `hash_eq`, `update_eq`,
`update_update_eq_hash`, `Crc32Spec.update_append`, `combine_eq`, `hasher_combine_eq`,
`combine_eq_hash`.
