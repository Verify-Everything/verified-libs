# Neovim status

Updated 2026-10-24. Upstream: neovim/neovim master `7b87ce822e6fd45a4d9993599c2854afdb0dc4dd` (2026-10-23).
Files: `/mnt/project-files/neovim-verify/` (see README.md there).

## Target 1: `src/nvim/base64.c` (226 lines). Status: first proofs done

Why: small, self-contained, clear spec (RFC 4648), and it decodes untrusted text (`vim.base64.decode`, used for terminal OSC 52 clipboard data).

Done:
- CBMC, 75 bounded proofs, all pass in 16 s: encoder matches an RFC 4648 reference byte for byte for every input up to 32 bytes; decoder is memory safe for any bytes up to 24 long and accepts only canonical Base64 (anything it accepts re-encodes to exactly the input); round trip decode(encode(x)) == x up to 16 bytes. No out-of-bounds, overflow, UB or leak at those sizes. All 6 planted bugs are caught.
- Frama-C WP, decoder: 68/68 goals proved for inputs of any length up to 2 GiB: no out-of-bounds access, no signed overflow, no bad shifts, output length <= 3/4 of input, failure returns NULL with length 0. Assumptions: 4 bit lemmas (checked separately with Z3 bit-vectors), one char/uint8 memory-model link, xmalloc never returns NULL, no frame (assigns) proof.

Finding (low severity, not reported upstream yet):
- For inputs longer than 2 GiB, `leftover_i = (int)src_i` wraps negative, so the padding check is skipped. Confirmed by running it: a 2^31+4 byte input with `=` at index 2^31 followed by `AAA` is ACCEPTED and returns 3 uninitialized heap bytes. The same shape at 8 bytes is rejected. LuaJIT caps strings just under 2 GiB, so it's likely only reachable in builds with PUC Lua. Repro: `neovim-verify/framac/over_2gib_repro.c`. A fix would be `size_t leftover_i` with a separate found flag.

Next:
- Frama-C proof of the encoder (its 64-bit fast path uses memcpy into uint64_t; expect memory-model work).
- Functional correctness of the decoder in WP (right now only CBMC covers it, bounded).
- Target 2 candidates, in order: UTF-8 helpers in `mbyte.c` (`utf_ptr2char`, `utf_ptr2len`, `utf_char2bytes`, `utf_char2len`), then `src/mpack/mpack_core.c` (msgpack parser for RPC, 579 lines, parses untrusted input). `math.c` is a quick extra (overflow-checked digit append, ctz/popcount).
