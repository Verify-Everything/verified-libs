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

## 2026-10-24 13:00 UTC update
- base64.c: all functions proved, zero admits (enc 259/259, dec 118/118 under 2 GiB, fixed dec 116/116 no limit), reproduced from clean with repo scripts.
- Published: https://github.com/blooddimmedtide/neovim_verifier (main). Fix PR: https://github.com/blooddimmedtide/verified_neovim/pull/1
- Status: candidate. Remaining gates: 35 reviewer mutants (base64/run_mutants.py, baseline-relative, resumable), ppc_32 run, fresh re-review, Yerin spec sign-off.
- Frama-C 33 string-literal bug: verification-notes/toolchain-bugs/.

## 2026-10-25 01:00 UTC
- base64.c: all machine gates pass (WP 260/120/118 with asserts on, 35/35 mutants, two reviews REVIEW.md + REVIEW2.md, CI twice in pinned container: runs 40129216377, 40140031727). Waiting on Yerin's spec sign-off; then status -> verified/fixed.
- CI lesson: Nix as root in a container needs /nix pre-created and /etc/nix/nix.conf with `build-users-group =` and `sandbox = false`; GitHub log blobs are blocked from the sandbox, so emit `::error::` annotations and read them via check-runs/<job>/annotations.

## 2026-11-02 ("fire on all cylinders")
- Choices made without waiting: target stays full functional correctness for every function (approved standard); base64.c stays candidate until Yerin signs off the spec.
- mbyte.c: 8 UTF-8 byte functions proved for every input with CBMC (libraries/neovim/mbyte/). CBMC takes ~2 s per function here, vs hours of WP work; use it for byte-level code with bounded loops.
- Finding #2: utf_cp_bounds_len, (int)(p - base) → UB / out-of-bounds read at >= 2 GiB (findings/cp-bounds-over-2gib.md). Fix: verified_neovim#2, branch fix-cp-bounds-over-2gib; all fixes together on branch `verified` (053a6f2), which CI now uses.
- Swarm prompt for other agents: neovim_verifier/docs/AGENT_PROMPT.md.
- Neovim full build is impossible in this sandbox (GitHub archive downloads return 403).

## 2026-11-02 03:30 UTC
- Candidates now 57 functions: base64 4, mbyte 8, mpack_core 23, math 7, memory.c string helpers 15.
- Reviews done: cp_bounds (accept with changes: harness now --object-bits 3, distances < 2^60), mpack (2 missing post-call checks added, all 20 runs re-proved, ShaDa makes the 4 GiB hang reachable in LuaJIT builds), math (wording only; MSVC _BitScanForward64 path of xctz and NetBSD popcount64 are open items). memory.c review running.
- memory.c: 15 functions proved with WP (333 goals). Tricks: pointer-quantified str_len, cvc5 --full-saturate-quant wrapper (tools/bin/cvc5-fsq), ghost length params, ghost lemma functions for count. See AGENTS.md lessons.
- Plugin track: telescope-fzf-native has two OOB reads (trailing_whitespaces, fzf_suffix_match; pattern ending in `$`). Findings + fix in neovim_verifier/plugins/telescope-fzf-native/. Upstream issue not filed yet. Proof of the fixed fzf.c next.
