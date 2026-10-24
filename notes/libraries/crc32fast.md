# crc32fast verification status

Upstream: github.com/srijs/rust-crc32fast @ d2363eab95ebc85fcf726d1c8fa845148e474591 (v1.5.3).
Tools: Aeneas/Charon nightly-2026.10.23-fdebf20, Rust nightly-2026-09-17, Lean 4.35.0.
Pipeline: /mnt/project-files/pipeline/libraries/crc32fast/ (common/ + 5 variants + 2 patches).
Old single-build layout backed up in crc32fast-work/pipeline-old/.

## Status (2026-10-24): NOT finished (admission gates still open)

Proved, standard axioms only, on the source with patches 0001 + 0002 applied:
- riscv64-portable (no_std): table, slow and slice-by-16 loops, hash, Hasher, combine.
- x86_64 and x86_64-std: SSE, AVX2 and AVX-512/VPCLMULQDQ kernels and CPU detection.
- aarch64 and aarch64-std: CRC32B/CRC32X instructions, byte and quad loops, the
  3-stream path for any align_to split, std feature detection.
- Hasher::update and Hasher::combine for every input (byte count wraps mod 2^64).

## Bug found
`Hasher::update` does `self.amount += len`. With `new_with_initial_len(u64::MAX)` this panics
in debug builds ("attempt to add with overflow", src/lib.rs:118) and wraps in release.
Fix (patch 0001): `wrapping_add` in update and combine. Not reported upstream yet (needs Yerin).

## Patches
- 0001-hasher-wrapping-add.patch: the bug fix above (behaviour change in debug only).
- 0002-simd-readable-by-aeneas.patch: x86 load helpers, aarch64 index loops and split_quads.
  No behaviour change intended; not yet proved equivalent (gate 1). Yerin is choosing between
  a verified fork and an equivalence proof.

## Open gates
- Gate 1: fork repo or equivalence proof for 0002 (waiting on Yerin).
- Gate 6: planted bugs picked by a fresh reviewer.
- Gate 7: forbidden scan flags `opaque` models (CPU feature flag, align_to split, fmt sink).
- Gate 8: differential tests (fork vs upstream, intrinsic models vs real CPU).
- Gates 5, 10: spec review and two reviews (Yerin's sign-off).
- Latent: `_mm256_castsi128_si256` / `_mm512_castsi128_si512` leave upper bits undefined
  per Intel; the code assumes zero. Model assumes zero; to be reported.
