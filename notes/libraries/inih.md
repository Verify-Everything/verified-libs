# inih (C INI parser): Frama-C verification status

Thread: "Verify inih with Frama-C". Last update: 2026-10-24 ~07:20 UTC.

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
- Helpers (`ini_rstrip`, `ini_lskip`, `ini_find_chars_or_comment`, `ini_strncpy0`): safety proved; `ini_strncpy0` also functional.
- `ini_parse_stream`: safety 147/167 goals. Open: lineno overflow (needs fix), loop-assigns inclusion of set-comprehension assigns, string-literal facts lost inside the main loop (the `";#"`, `"]"`, `"=:"` literals), several call preconditions in the name=value branch.
- Not started: ini_reader_string, ini_parse_string(_length), ini_parse_file, ini_parse, functional model, config matrix, planted bugs.
- C++ wrapper: Yerin decided 2026-10-24: admit the C library only; INIReader gets bounded ESBMC checks under candidates/ (not verified).
- Working files: proof copy and prelude in the inih thread's scratchpad for now; will move to pipeline/libraries/inih/.

## Findings so far
1. `lineno` is a signed `int` incremented once per line with no bound. A stream with more than INT_MAX (about 2.1 billion) lines overflows it, which is undefined behavior in C. Eva and WP both flag it. Only reachable with `ini_parse_stream`/`ini_parse_file` on a huge input.
2. `ini_parse_file` passes `fgets` cast to `ini_reader` (`char*(*)(char*,int,void*)`), but fgets takes `FILE*`. Calling through an incompatible function pointer type is undefined behavior by the C standard (6.3.2.3p8), although it works on every common ABI. Frama-C's kernel warns about it.
3. Earlier upstream bug (fixed in 8e06f6b, Oct 2025): `abyss[strlen(abyss) - 1]` read out of bounds on an empty chunk. Used as a regression check for the proof.

## Pitfalls hit (Frama-C/WP)
- See general.md for the cross-library list.
