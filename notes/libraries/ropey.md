# ropey 1.6.1 status

Thread: "Verify ropey for Helix". Work: /mnt/project-files/ropey-verify/ (extract/, kani/, lean/ as they appear).
Source: crates.io ropey-1.6.1.crate, sha256 93411e42...93b5 (= Helix Cargo.lock checksum; same files as git tag v1.6.1, d41ee24).
Build Helix uses: `default-features = false, features = ["simd"]` (LF-only lines). helix-core's `unicode-lines` feature turns on
ropey `unicode_lines` (CR and Unicode breaks), so both line modes are in scope.
NOT finished. Proved so far (Lean, real extracted code, only propext/Classical.choice/Quot.sound): see tracker.

## Scope
Helix calls about 45 public methods (counted by grep over Helix @ ba40e54, non-test): Rope/RopeSlice new, from_str, slice, insert,
remove, insert_char, append, split_off, len_chars/bytes/lines, line, line_to_char/byte, char_to_line/byte, byte_to_char/line,
char, byte, get_char, get_slice, byte_slice, chars/chars_at, chunks/chunk_at_byte, lines/lines_at, bytes/bytes_at, as_str,
char_to_utf16_cu, try_* variants, RopeBuilder, from_reader, str_utils::byte_to_char_idx, iterator next/prev/reverse, plus
Clone/PartialEq/Display/Hash/From impls. These reach almost all of ropey's internals (tree/, str_utils, crlf), so the
practical scope is the whole crate (~14k lines incl. tests, ~670 functions after extraction).

Dependencies that ropey itself pulls in (each is NOT std, so each is an open assumption until verified):
- str_indices 0.4.3 with `simd` (chars::count/from_byte_idx/to_byte_idx, lines_lf::*, utf16::*; SSE2 code on x86_64).
- smallvec 1.x (RopeBuilder stack, NodeSmallString backing store). Shared with the smallvec entry.

## Extraction result (2026-10-24 14:10 UTC, Charon build 5 + Aeneas build 11 + frozen-capture patch)
Toolchain: helix-verify/toolchain (Charon build 5, Aeneas build 11) plus ropey-verify/tool-patches/
aeneas-build11-frozen-mut-capture.patch (sent to the Aeneas thread, not yet in a build).
Dependencies resolved to Helix's Cargo.lock: str_indices 0.4.3, smallvec 1.15.2 (extract/Cargo.lock.helix-deps;
the output is identical with ropey's own lock, 0.4.2 / 1.11.1, since both are external calls).
Lean files: `extract/tools/assemble.sh AENEAS_OUT LEAN_PROJECT` (postprocess + external models, asserts no axiom).
`lake build Ropey` succeeds; no axioms. 19 bodies not translated (each is `sorry`, so nothing about them can be proved):
- Chunks::new_with_range_at_byte, Chunks::next_impl/prev_impl, Lines::next_impl/prev_impl: nested borrows (the Aeneas
  thread is on these). These block `chars()` and `chunks()`.
- RopeSlice::new_with_byte_range; RopeSlice eq/cmp/hash/Display; Rope::from_reader (io::Error is dyn);
  Node::assert_integrity; Debug impls. Not in Helix's listed API.
The 10 Helix functions (len_chars, slice, insert, remove, line, line_to_char, char_to_line, char_to_byte, chars, chunks)
reach 258 functions and 81 external functions. All of them translate except the Chunks constructor/iterators above.

## External functions (trusted base, see CLAIM.md)
- Rust std: lean/models/Std.lean.in (Arc as the value itself, Option, RangeBounds, slice last/last_mut/copy_within,
  str len/is_empty/is_char_boundary/indexing, from_utf8_unchecked, String). UB is `fail .undef`, panics `fail .panic`.
- smallvec 1.15.2 and str_indices 0.4.3: lean/models/Deps.lean.in. Open assumptions until those entries prove them.
  SmallVec::spilled is an unknown function (proofs must hold for any value).
- node_children::inner: lean/models/NodeChildrenInternal.lean.in, checked by Kani on the real unsafe code.
- Differential test: difftest/models (104,000 cases, 0 mismatches).
- Everything else stays `opaque` (79 functions; Debug/Display/io/hash and others outside the call graph).

## Plan
1. Unsafe core (node_children::inner = fixed-capacity arrays of Arc<Node>, 14 fns; node_text::inner = NodeSmallString, ~11 fns):
   Kani proofs on the real code that each function matches a Vec/String spec. Capacity is a constant, so a proof for every length up
   to capacity covers every input. These specs become the definitions used in Lean for the opaque inner functions.
2. Arc: modelled as a plain value (make_mut = copy-on-write gives the same observable values). Needs a stated std model + difftest.
3. Safe layer in Lean on the real extraction: tree invariants, then each Rope method's full functional spec on a list-of-chars view.
4. RopeSlice and iterator parts Aeneas can't read: try an Aeneas fix or newer release first; else another tool (Verus download is
   blocked here for now: github release assets 404 without the API; Kani with function contracts is the fallback).
5. str_indices and smallvec: separate entries (str_indices includes SIMD intrinsics).

## Current toolchain (2026-10-24 15:30 UTC)
Charon build 6 + Aeneas build 13 + Lean library build 14 (helix-verify/toolchain). All proofs recheck with build 14.
No proof uses size_hint. Proofs: ropey-verify/lean/Ropey/Proofs/ (build: `lake build Ropey`).

## Per-function tracker (LF-only build, as Helix uses)
Text view: `text r` = the chars of the tree. `RopeInv` = valid tree (UTF-8 leaves, 1..24 children, stored infos
correct) and bytes < usize::MAX. `LeavesNonempty` = no empty leaf unless the rope is empty (ropey's own
assert_node_size rule); insert/remove must show they keep it.
- V len_chars, len_lines.
- V char_to_byte, try_char_to_byte (exact Err), char_to_line, try_char_to_line, line_to_char, try_line_to_char.
- V slice, get_slice: for any RangeBounds impl; result = chars a..b; panics/None exactly when not a ≤ b ≤ len.
  Assumes the bound `+1` does not overflow (Excluded start / Included end = usize::MAX), which Aeneas treats as a panic.
- V line, get_line: line k with its LF; needs LeavesNonempty. Without it the statement is false (an empty first leaf
  would make line 0 empty), so insert/remove proofs must keep that rule.
- X insert: BUG found (see Findings). V on the fixed code: `insert_spec`, `try_insert_spec` (InsertBig.lean),
  all text sizes. Result keeps RopeWF (valid tree, balanced `Node.Ht`, no empty leaf, no leaf seam inside CR LF)
  and text = take c ++ ys ++ drop c. Assumes bytes(text) + bytes(ys) + 981 <= usize::MAX and tree height
  < usize::MAX (each level is a heap node, so this holds in any real address space; listed in CLAIM.md).
  Parts: Insert/InsertLoop (chunked path, texts <= 6*984 bytes); big path = from_str (Builder, Builder2, Builder3:
  `rope_from_str_spec`, also bounds the height by the text length), split_off (SplitOff), append (Append,
  CrlfSeam, FixTreeSeam). All axiom-clean (propext, Classical.choice, Quot.sound). (2026-10-24 20:30 UTC)
- V remove, try_remove: `remove_spec`, `try_remove_spec` (RemoveTop.lean), any RangeBounds. Result keeps RopeWF
  and text = take a ++ drop b; try_remove gives Err with the rope unchanged unless a <= b <= len; remove panics then.
  Assumes bytes(text) < usize::MAX and the same bound `+1` fit as slice. remove's code is the same in stock and fixed
  1.6.1 (the insert fix only touches Rope::insert), so this holds for stock ropey too.
  Parts: Remove (leaf case), RemoveSearch, RemoveMerge (merge closure and loops), RemoveRec (`RCPost`, per-child
  step), RemoveSeam, RemoveInternal, RemoveStep (internal nodes; `rcr_ih_all`: remove_char_range for every
  tree height), RemoveTop. Axiom-clean (propext, Classical.choice, Quot.sound). (2026-10-24 ~21:30 UTC)
- V Bridge to HelixCommon (Proofs/Bridge.lean): `model r` (text + leaf start offsets) meets the shared `WF`
  (`model_wf`), and len_chars, char_to_line, line_to_char, char_to_byte, get_char, slice, line, insert, remove
  are restated in the shared model's terms (`*_model`, LF-only). Axiom-clean. Not covered: the iterator and
  chunk parts of the shared model (Chars, chunkAtByte, contiguous, pieces), which need chunks.
- Draft claim card: ropey-verify/CLAIM.md (status candidate; lists tool patches and all FunsExternal models).
- V chars, chunks (Creusot, 2026-10-25): every Chunks and Chars function proved on ropey's own source
  (constructors, next/prev_impl, next, prev, reverse, size_hint, IteratorSpec laws), plus get_chunk_at_char.
  143 proof files, 0 failed. Strip check: annotated source minus ghost lines == stock 1.6.1. Trusted str and
  str_indices contracts difftested (3.8M checks, 0 mismatches). Details: ropey-verify/creusot/README.md.
  Lean link: Proofs/SliceShape.lean proves the preconditions (shape_of_wf, slice_shape); the rest is on
  paper (creusot/LINK.md). Open: derived Clone
  for Chunks/Chars, termination, line offsets of the Chunks constructors.
- V Kani: full run 1030 harnesses, 0 failures (2026-10-25).

## Findings
1. insert puts a leading '\n' in the wrong place (silent wrong text) after leaf compaction. Stock 1.6.1, public API,
   Helix features. 2-line fix; ropey tests pass. Files: ropey-verify/findings/insert-newline-compaction/
   (README, repro, fix patch, upstream issue draft). Not filed upstream yet (asked Yerin).

## 2026-10-26: non-vacuity checks (project rule)
- Lean: lean/Ropey/Proofs/NonVacuity.lean applies all 21 main and Bridge theorems to a concrete
  rope ("ab") with concrete arguments and gets concrete results. Same 3 axioms.
- Checked against the editing-helpers traps: no `Unit` external types, no "succeeds for every
  index" hypotheses.
- Creusot: planted-false smoke test on all 31 functions passes (creusot/vacuity/). Two defensive
  `return None` lines in Chunks next_impl/prev_impl are unreachable by the invariant (dead code).

### 2026-11-02: strict chunk-at-byte spec
- Added `node_get_chunk_at_byte_spec_strict` (Builder2.lean): the returned chunk ends strictly after the byte index unless it is the last chunk. Requested by the Helix editing-helpers thread for RopeSlice::line. Axioms: the 3 allowed.

### 2026-11-02: audit for the Charon build 6 match-guard bug and third-party interior mutability
- Re-extracted ropey 1.6.1 with `--mir elaborated` (same flags as r19, Charon build 6, Aeneas build 13): ~/ropey/work/r20.llbc, o20/.
- Both extractions have 40 `fail panic` sites, in the same functions with the same counts per function. No panic arm appears or disappears, so no suspect arm. (All 40 are unreachable!() arms on Leaf/Internal and explicit panics.)
- Other differences are loop renaming and 7 more untranslated bodies in the elaborated version (27 vs 20 sorry). The proofs keep using the default-MIR extraction.
- No lock_api, parking_lot, once_cell, arc_swap or cell types in the extraction (Arc only).
- smartstring and smallvec do not use Charon/Aeneas (Kani, Creusot and hand-written Lean models), so neither issue applies.
- 2026-11-02 (from the toolchain thread): Aeneas build 17 with Charon build 7 also translates RopeSlice::new_with_byte_range and Rope::from_reader (toolchain README item 30). Not yet re-extracted here. The Helix editing-helpers thread is working on byte_slice, Chars, Chunks and Lines.
