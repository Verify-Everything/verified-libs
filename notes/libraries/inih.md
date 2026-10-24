# inih (C INI parser): Frama-C verification status

Thread: "Verify inih with Frama-C". Last update: 2026-10-24 ~08:10 UTC.

## Target
- Upstream: https://github.com/benhoyt/inih, commit 2bbdec4 (r62 + 3 commits, 2026-09-28). `ini.c` 330 lines.
- Default build options (INI_USE_STACK=1, multiline, BOM, inline comments on).

## Tooling
- Frama-C 32.1 in Docker with Alt-Ergo 2.5.4, Z3 4.13.4, CVC5 1.2.1. See general.md (inih heading) and `frama-c/`.

## Approach
- Proof copy of `ini.c` with ACSL contracts and loop invariants. A script strips the annotations and diffs against upstream, so the proven code is byte-identical to upstream.
- Reader and handler are function pointers. The proof routes them to two abstract functions with contracts (any fgets-like reader; any handler that follows the API docs). So the result covers every reader and handler meeting those contracts.

## Status (against the verified-libs admission standards)
- Spec for review (gate 5): https://claude.ai/artifact/FrQVR3eY8rgF4SdE5zFUZQ, waiting on Yerin.
- Helpers (`ini_rstrip`, `ini_lskip`, `ini_find_chars_or_comment`, `ini_strncpy0`): safety proved (rstrip 31/31, find 35/35); `ini_strncpy0` also functional.
- Prelude lemmas (ini_nul_at / ini_nonnul / ini_str_len helpers): 8/8 proved. No unproved lemmas left (the old strlen_frame lemma was removed).
- `ini_parse_stream`: safety 197/202 goals, then the section branch was fixed too (now 4 open). Open: lineno overflow (needs the fork fix), and three call preconditions on string literals (`strchr(";#", ..)`, `find(.., "]")`, `find(.., "=:")`) where WP loses the literal's contents inside the main loop.
- Note for the build matrix: with INI_ALLOW_INLINE_COMMENTS=0, `ini_rstrip(value, end)` is called with end < value (end still points at the '='). The loop guard makes it a no-op and the line was already trimmed, so behavior is fine, but rstrip's contract needs a no-op case for that build.
- Not started: ini_reader_string, ini_parse_string(_length), ini_parse_file, ini_parse, functional model, config matrix, planted bugs.
- C++ wrapper: Yerin decided 2026-10-24: admit the C library only; INIReader gets bounded ESBMC checks under candidates/ (not verified).
- Working files: proof copy and prelude in the inih thread's scratchpad for now; will move to pipeline/libraries/inih/.

## Findings so far
1. `lineno` is a signed `int` incremented once per line with no bound. A stream with more than INT_MAX (about 2.1 billion) lines overflows it, which is undefined behavior in C. Eva and WP both flag it. Only reachable with `ini_parse_stream`/`ini_parse_file` on a huge input.
2. `ini_parse_file` passes `fgets` cast to `ini_reader` (`char*(*)(char*,int,void*)`), but fgets takes `FILE*`. Calling through an incompatible function pointer type is undefined behavior by the C standard (6.3.2.3p8), although it works on every common ABI. Frama-C's kernel warns about it.
3. Earlier upstream bug (fixed in 8e06f6b, Oct 2025): `abyss[strlen(abyss) - 1]` read out of bounds on an empty chunk. Used as a regression check for the proof.

4. Toolchain: Frama-C WP (32.1 and 33) assumes `const char a[] = "..."` is all zeros (see toolchain-bugs/). inih has no such arrays, so its proofs don't rely on it. CLAIM.md will list a check for it.

## Pitfalls hit (Frama-C/WP)
- See general.md for the cross-library list.
