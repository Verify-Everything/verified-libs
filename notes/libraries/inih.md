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
Last update: 2026-10-26 ~14:00 UTC. Safety (memory safety + no UB, -wp-rte) only so far; functional proof waits on spec sign-off.
- Spec for review (gate 5): https://claude.ai/artifact/FrQVR3eY8rgF4SdE5zFUZQ, waiting on Yerin.
- Helpers rstrip 31/31, lskip, find 35/35, strncpy0 (also functional): proved. Prelude lemmas 8/8 proved.
- ini_reader_string 46/46 and ini_parse_string / ini_parse_string_length 24/24 (Typed+Cast model, string mode).
- ini_parse_stream, three proof modes (prelude #ifdef): generic reader (contract R), string reader, file reader (fork only).
  Upstream: all goals except the lineno overflow (finding 1) in generic and string modes, with 1-2 goals still flaky between runs.
  Fixed fork: generic 224/225 and file 231/233 in the last full run; remaining goals prove alone with the new strategy. Full rerun in progress.
- Fork (inih-work/fork/inih-fixes.patch): lineno saturates at INT_MAX; ini_parse_file uses a static fgets wrapper. All upstream test baselines unchanged.
  ini_reader_file, ini_parse_file, ini_parse: 35/35 on the fork. Upstream ini_parse_file/ini_parse cannot be verified (UB in the fgets cast): status "fixed".
- Proof tooling: custom WP strategy plugin inih-work/prune/inih_prune.ml (only removes hypotheses; trusted, list in CLAIM.md). Built inside the Frama-C image.
- Assumptions to list in CLAIM.md: WP Typed memory-model separation hypotheses; Typed+Cast for void* -> ctx/FILE round-trip casts; reader/handler contracts R and H; Frama-C libc specs of fgets/fopen/fclose/strchr/strlen; the prune plugin; Frama-C string-init bug not triggered.
- Reproducibility: two full no-cache runs of the fixed fork match (2026-10-24): generic 343/343, string mode 313/313, file mode 272/272, lemmas 8/8. Summaries in inih-work/logs/.
- Planted bugs (safety level, inih-work/mutants.py): 12 of 13 make the proof fail, including the regression of upstream bug 8e06f6b (M01). M04 (lskip skips every char) is memory-safe, so only the functional proof can catch it.
- Build-option matrix (generic mode, fork), 2026-10-24 ~18:40 UTC: default 354/354; BOM=0 339/339; STOP_ON_FIRST_ERROR=1 386/386; HANDLER_LINENO=1 343/343; MAX_LINE=20 343/343; ALLOW_NO_VALUE=1 357/357; MULTILINE=0 318/318; CALL_HANDLER_ON_NEW_SECTION=1 367/367; INLINE_COMMENTS=0 315/317 (fix written, rerun in progress).
  Annotation changes for this: prev_name annotations go through INI_IF_ML() (prev_name only exists with multiline); ini_rstrip got a "noop" behavior for end < s (happens with INLINE_COMMENTS=0, where rstrip(value, end) gets end before value; no UB, nothing is changed).
- Heap mode: the first "all proved" results (2026-10-24 ~20:50) were WITHDRAWN (the allocator model had a contradiction, so the proofs were vacuous). New model (2026-10-25): abstract heap-block predicate + admitted freshness after each allocation; realloc writes no memory and keeps contents. Plain heap 365/365; realloc fully proved with -wp-timeout 300 and one hint. Non-vacuity: INI_INITIAL_ALLOC=1 now fails exactly on its out-of-bounds read; smoke tests pass; a concrete pool allocator meets the contracts (witness/).
- Non-vacuity witnesses (project rule 2026-10-26): inih-work/witness/witness.c, proved by WP: reader/handler/allocator realizations + concrete calls of every helper and entry point (default 69/69, string 13/13, file 13/13, heap 10/10, allocator 28/28; smoke tests all pass).
- Edge sizes: INI_MAX_LINE=1 and INI_INITIAL_ALLOC=1 read line[-1] (`line[offset - 1]` with offset 0). README says INI_MAX_LINE must be 3 more than the longest line, but nothing enforces it. Fork fix staged (finding 5), which also covers INI_MAX_SECTION=0 and INI_MAX_NAME=0. INI_MAX_LINE=2 and INI_MAX_SECTION=INI_MAX_NAME=1 prove. Numeric options are proved at sampled values (boundaries plus defaults), not symbolically.
- Full rerun of 23 configurations with smoke tests in progress (2026-10-26).
- Not done: heap mode results, string/file modes per build option, combinations, tiny INI_MAX_LINE edge configs, functional proof, C++ bounded checks, pipeline adoption.
- C++ wrapper: Yerin decided 2026-10-24: admit the C library only; INIReader gets bounded ESBMC checks under candidates/ (not verified).
- Working files: inih-work/ (annotated copy, prelude, run scripts, make_fix.py builds the fork proof copy).

## Findings so far
1. `lineno` is a signed `int` incremented once per line with no bound. A stream with more than INT_MAX (about 2.1 billion) lines overflows it, which is undefined behavior in C. Eva and WP both flag it. Only reachable with `ini_parse_stream`/`ini_parse_file` on a huge input.
2. `ini_parse_file` passes `fgets` cast to `ini_reader` (`char*(*)(char*,int,void*)`), but fgets takes `FILE*`. Calling through an incompatible function pointer type is undefined behavior by the C standard (6.3.2.3p8), although it works on every common ABI. Frama-C's kernel warns about it.
3. Earlier upstream bug (fixed in 8e06f6b, Oct 2025): `abyss[strlen(abyss) - 1]` read out of bounds on an empty chunk. Used as a regression check for the proof.

4. Toolchain: Frama-C WP (32.1 and 33) assumes `const char a[] = "..."` is all zeros (see toolchain-bugs/). inih has no such arrays, so its proofs don't rely on it. CLAIM.md will list a check for it.

5. Size options with no lower bound (2026-10-26). Confirmed with AddressSanitizer through ini_parse_file: INI_MAX_LINE=1 reads line[-1] (stack underflow); INI_USE_STACK=0 with INI_INITIAL_ALLOC=1 reads line[-1] (heap overflow); INI_MAX_SECTION=0 and INI_MAX_NAME=0 write past a zero-length array (ini_strncpy0 with size 0). Upstream only documents a minimum for INI_MAX_LINE and enforces none. Fork fix applied (2026-10-28): four `#error` guards after `#include "ini.h"` (MAX_LINE >= 2, heap INITIAL_ALLOC >= 2, MAX_SECTION >= 1, MAX_NAME >= 1). Not filed upstream; ask Yerin first.

6. Read failure during line growth (2026-10-28). With INI_USE_STACK=0 and INI_ALLOW_REALLOC=1, when the reader returns NULL while a long line is being extended, the parser `break`s and goes on to parse the buffer. A reader may write bytes and still return NULL: glibc fgets does exactly that on a read error (it stores what it read and writes no terminator; C11 7.21.7.2 says the contents are indeterminate). The old terminator is overwritten, so strlen / ini_find_chars_or_comment read past the heap block. Found because WP could not prove `cells2` once the grow loop was live; confirmed with AddressSanitizer on upstream 2bbdec4 (edge test rr.c: reader fills a long line, then returns NULL after n-1 bytes). Fork fix: `line[offset] = '\0';` before the `break`. Rare in practice (needs an I/O error mid-line, or a custom reader that behaves like fgets). Not filed upstream; ask Yerin first.

## Pitfalls hit (Frama-C/WP)
- See general.md for the cross-library list.

## 2026-10-27 rerun notes
- With INI_ALLOW_REALLOC=1 and default sizes (INI_INITIAL_ALLOC = INI_MAX_LINE = 200), smoke tests show the whole buffer-grow loop (ini.c lines 276-290) is dead code: the buffer already has its maximum size. That is true of the real code, not a proof error, but it means those builds never check the grow path. The realloc builds are now run with INI_INITIAL_ALLOC=64 (and 2 with INI_MAX_LINE=3), where the loop is live, plus the default sizes.
- INI_MAX_LINE=2 and INI_MAX_SECTION=INI_MAX_NAME=1: all safety goals prove; smoke tests flag code those sizes can never reach (BOM skip, sections, continuation lines). Expected.
- Several heap builds had 2-5 goals time out while two runs shared the machine. They are retried one build at a time with a longer limit (scripts: inih-work/chain.sh, runrest2.sh, runrealloc.sh, retry.sh; all resume after a machine restart).
- The one "Unreachable" item in the default build's WP summary is the generated exit condition (`exits \false`) of ini_strncpy0, which has no exit() call. It is not a vacuous goal. (Found with `-then -report`.)

## 2026-11-01 rerun after two annotation changes
- The first full run left 3 goals open in the realloc string and FILE builds (INITIAL_ALLOC=64). They still timed out without the WP cache.
- FILE build: Frama-C's fgets contract has no length bound, so `strlen(line) < max_line` was not provable on the heap. Added `admit ensures fgets_len` to ini_reader_file (C11 7.21.7.2p2). It is listed in vpipe.toml [trust].
- String build: `keep` after the handler call took 3-5 minutes and timed out under load. Added hint `h_vsep` (value lives in line, and line is separate from section and prev_name; realloc builds only).
- Both builds now prove these goals (5/5 and 8/8, no cache). Strip checks: SAME and FIXSAME. The full 45-build run restarted 2026-11-01 about 08:30 UTC.
