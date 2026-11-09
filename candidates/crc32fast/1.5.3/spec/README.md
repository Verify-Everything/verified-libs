# crc32fast 1.5.3: specification

crc32fast computes the standard CRC-32 (ISO-HDLC, reflected polynomial 0xEDB88320, init and final XOR 0xFFFFFFFF). Every public function returns the CRC the bit-at-a-time reference gives, for any input, on the five verified builds (riscv64 no_std; x86_64 no_std and std with the SSE, AVX2 and AVX-512 kernels; aarch64 little-endian no_std and std); incremental updates and combine equal a single pass; no public function panics. Not verified: i686, aarch64_be, no_std builds with SIMD target features enabled, rustc 1.80-1.88.

## Properties (success criteria, from vpipe.toml [scope].properties)

- update_slow, update_fast_16, every SIMD kernel (SSE, AVX2, AVX-512, aarch64 CRC32) and hash equal the bit-at-a-time reference CRC-32, for inputs of any length
- Hasher::update then finalize equals hash of the concatenated input (incremental = single pass), with any kernel State::new picks
- combine and Hasher::combine equal the CRC of the concatenation
- No public function panics or fails on any input (internal helpers such as get*/fold_16 are proved under the length conditions every caller meets); the u64 byte count wraps modulo 2^64 (fix in fork commit 990c6c1; upstream panics in debug builds)
- Debug writes exactly `crc32fast::Hasher`; Clone, Default, Hash::write/finish behave as documented

## Formal spec files (in proof/)

- common/Crc32fast/Spec.lean
