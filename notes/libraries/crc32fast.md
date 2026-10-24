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

## Pipeline run (2026-10-24, vpipe 0.2.4)
All 5 variants prove: 1151/1151 theorems, standard axioms only. Gates passed: all inputs, cross-check.
Cross-checks (crosscheck/ in the library folder, run by vpipe):
- diff.sh: patched tree vs bitwise reference vs pristine upstream on every kernel (x86 portable,
  SSE, AVX2, AVX-512, std; aarch64 crc, portable, std under qemu). An instrumented copy confirms
  which kernel runs. All match; upstream panics on the overflow case, the fix wraps.
- models.sh: the Lean models of all 27 x86 intrinsics vs this CPU (108k cases per run) and the
  aarch64 CRC32B/CRC32X models vs qemu (40k). 0 mismatches. Planted mismatches are caught.

## Open gates
- Gate 1: fork repo or equivalence proof for 0002 (waiting on Yerin).
- Gate 6: planted bugs picked by a fresh reviewer; `vpipe mutate` does not support variants yet (asked).
- Gate 7: opaque models now allowed (0.2.4); x86 leanchecker replay OOMs with all modules in one call (asked pipeline thread to batch).
- Gate 2: inventory ignores functions.toml in variant runs (asked pipeline thread).
- Gate 9: clean reproducible runs in a pinned container.
- Gates 5, 10: spec review and two reviews (Yerin's sign-off).
- Latent: `_mm256_castsi128_si256` / `_mm512_castsi128_si512` leave upper bits undefined
  per Intel; the code assumes zero. Model assumes zero; to be reported.
