# inih (C INI parser): Frama-C verification status

Thread: "Verify inih with Frama-C". Last update: 2026-10-24 ~05:00 UTC.

## Target
- Upstream: https://github.com/benhoyt/inih, commit 2bbdec4 (r62 + 3 commits, 2026-09-28). `ini.c` 330 lines.
- Default build options (INI_USE_STACK=1, multiline, BOM, inline comments on).

## Tooling
- Frama-C 32.1 in Docker with Alt-Ergo 2.5.4, Z3 4.13.4, CVC5 1.2.1. See general.md (inih heading) and `frama-c/`.

## Approach
- Proof copy of `ini.c` with ACSL contracts and loop invariants. A script strips the annotations and diffs against upstream, so the proven code is byte-identical to upstream.
- Reader and handler are function pointers. The proof routes them to two abstract functions with contracts (any fgets-like reader; any handler that follows the API docs). So the result covers every reader and handler meeting those contracts.

## Status
- Helpers (`ini_rstrip`, `ini_lskip`, `ini_find_chars_or_comment`, `ini_strncpy0`): all WP goals proved, including that `ini_strncpy0` copies exactly min(len, size-1) chars and NUL-terminates.
- `ini_parse_stream`: in progress.

## Findings so far
1. `lineno` is a signed `int` incremented once per line with no bound. A stream with more than INT_MAX (about 2.1 billion) lines overflows it, which is undefined behavior in C. Eva and WP both flag it. Only reachable with `ini_parse_stream`/`ini_parse_file` on a huge input.
2. `ini_parse_file` passes `fgets` cast to `ini_reader` (`char*(*)(char*,int,void*)`), but fgets takes `FILE*`. Calling through an incompatible function pointer type is undefined behavior by the C standard (6.3.2.3p8), although it works on every common ABI. Frama-C's kernel warns about it.
3. Earlier upstream bug (fixed in 8e06f6b, Oct 2025): `abyss[strlen(abyss) - 1]` read out of bounds on an empty chunk. Used as a regression check for the proof.

## Pitfalls hit (Frama-C/WP)
- See general.md for the cross-library list.
