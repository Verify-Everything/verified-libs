# Helix status

Thread: "Start verifying Helix". Upstream: github.com/helix-editor/helix master @ ba40e547426b0f9896c8bdc699a4ab11f2b37dbc (2026-09-29).
Prior work search (2026-10-24): none found for the editor (only an unrelated Coq project also named HELIX). Upstream has quickcheck tests only.
Work lives in /mnt/project-files/helix-verify/ (model crate, difftest, Lean project without .lake).

Rule from Yerin (2026-10-24): not finished until every function is verified or has a verified fix.

## Scope and size (non-test fns, rough grep count)
| crate | lines | fns | verifiable with Aeneas/Lean? |
|---|---|---|---|
| helix-core | 20k | ~600 | mostly yes (pure text logic); syntax.rs (~100) wraps tree-sitter FFI: no |
| helix-stdx | 2.7k | ~140 | partly (rope/str helpers yes; path/env/fs no) |
| helix-parsec | 0.6k | ~19 | yes |
| helix-view, helix-term, helix-tui, helix-lsp(-types), helix-dap(-types), helix-vcs, helix-loader, helix-event | ~83k | ~3000 | essentially no: UI, async, IO, network, git, terminal |

## Per-module tracker (helix-core)
Legend (old): V = proved on the safe MODEL crate (Aeneas, no sorry) + difftest vs upstream, D = differential-tested only, O = open.
**Under the verified-libs standard (2026-10-24) every "V" below is only `tested`**: the proofs are about the model crate, not
the real code. They must be re-done on the real extraction (see helix-method.md). Bugs below are confirmed on real upstream,
but their fixes are proved only on the model.

### transaction.rs (41 fns)
- V `ChangeSet::with_capacity`, `retain`, `delete`, `insert` (match list builders, no overflow, len/len_after right)
- V `ChangeSet::compose` (no panic on well-formed inputs; apply(compose a b) = apply b ∘ apply a)
- V `ChangeSet::invert` (no panic; inverse turns edited doc back into original; lengths swap)
- V `Transaction::change` / `ChangeSet::from_changes` core loop (sorted edits: applies = splice)
- V `Transaction::delete` core (`delete_ranges`): no panic for from<=to<=len, sorted or not; for ranges sorted by start, deletes exactly the covered positions
- V `ChangeSet::apply` semantics (spec `apply`; matched against upstream by difftest)
- FIXED+V `ChangeSet::new(doc).invert(doc)` returned len 0 (proved: invert_new_bug). Fix `invert_fixed` proved (invert_fixed_spec); patch in helix-verify/patches/invert-identity.patch, not filed upstream
- V `map_pos` (never panics for pos <= len; result = spec `mapPos`, and <= len_after). Lean: PosTop.lean `map_pos_spec`, `mapPos_le`
- V `update_positions` on sorted positions (= map_pos per position). Lean: `update_positions_spec`
- BUG+FIXED+V `update_positions` on UNSORTED positions: a position at an insertion point that was already passed is mapped through the next Retain (wrong offset). Example: changes [Insert("ab"), Retain(3)], positions [(1,Before),(0,Before)] gives [3,2], map_pos gives [3,0]. Confirmed on real upstream (difftest: 586 of 200k random cases; and a unit test). Realistic trigger: diagnostic end positions (helix-view document.rs). Fix (restart from the first change when pos < last mapped pos) proved for ANY order: `update_positions_fixed_spec`. Patch with regression test: helix-verify/patches/update-positions-unsorted.patch (test fails before, passes after; all transaction tests pass). Not filed upstream.
- V `is_empty` (true iff no ops or single Retain(len); then apply is identity), `Operation::len_chars`, `Assoc::{stay_at_gaps, insert_offset, sticky}`
- O `ChangeSet::apply` (on code), `changes`, `changes_iter`/`ChangeIterator`, `Transaction::{new, changes, selection, apply, invert, compose, with_selection, change_ignore_overlapping, change, delete, insert_at_eof, change_by_selection*, delete_by_selection*, insert, changes_iter}`, `From<ChangeSet>`
- `ChangeSet::map` is `unimplemented!()` upstream (always panics, never called)
### selection.rs (65 fns), position.rs (17 fns) — thread "Verify Helix selections"
Work: /mnt/project-files/helix-verify/selection/ (model/, lean/, difftest/, axioms/, real/ for the real-code bridge), helix-verify/position/.
- MODEL-PROVED (does not count yet under the admission standard): all 65 selection.rs functions except derived Debug impls, on an Aeneas-extracted model crate. 231 theorems, std axioms only. Difftest vs upstream: 200k cases per function, no mismatch inside preconditions.
- Model choices: text = &[u32] chars, LF-only lines (default ropey build; `unicode-lines` feature open), grapheme boundaries / regex matches / tree-sitter offsets as inputs, SmallVec->Vec, sort_unstable->insertion sort (pass proofs hold for any sorted input).
- In progress: proof that the real helix-core code equals the model (Charon reads real helix-core; Aeneas fails only on the fn-item `Range::from` used as a closure and on update_positions).
- O: Debug impls (Range, Selection), `unicode-lines` feature, map_no_normalize size cap (model needs 2*len <= usize::MAX), ropey/smallvec/unicode-segmentation/regex/tree-house behaviour (trusted until those crates are verified).
- Findings (not filed): transform_iter keeps a stale primary_index (panics if 2 <= count <= pi; invalid selection if count < 2); Selection::new with bad primary index and 1 range returns an invalid selection; is_subset / Selection::contains doc comments not exact ([0,3] vs point 3 gives false); LineRangeIter::next underflows on unsorted selections (reachable via primary_mut / map_no_normalize); merge_consecutive_ranges does not sort.
- position.rs: model proofs in progress (worker), bridge to real code not started.
### Parsers/utilities thread ("Verify Helix parsers": command_line, snippets/*, uri, fuzzy, diff, editor_config, config, diagnostic)
Work dirs: helix-verify/command_line/, helix-verify/snippets_parse/, helix-verify/snippets_render/, helix-verify/utils/ (each has STATUS.md).
- BUG editor_config.rs `is_glob_relative`: `idx = ... |close| idx + close` should be `open + close`.
  (a) panic: section header `[éé[ab]]` -> slices str at byte 3 inside 'é' -> Helix panics when an .editorconfig with it is read.
  (b) wrong answer: `ab[c][d/]` returns true although the only '/' is inside brackets. Confirmed by running upstream code. Needs verified fix.
- All other functions in these modules: O (in progress).
### movement.rs, textobject.rs, match_brackets.rs, surround.rs, object.rs, search.rs (72 fns) — thread "Verify Helix movement and objects"
Work: /mnt/project-files/helix-verify/motion/ (model crate, Lean project HelixMotion, difftest/run_difftest.sh).
Text model: RopeSlice = list of `Ch` (code point + Unicode facts as data: grapheme boundary, White_Space, alphanumeric,
punctuation category, lower/upper, width). Proofs hold for any values of those tables. Lines: default build (`unicode-lines` off, only \n).
Shared layer (text.rs: categorize_char, graphemes, lines, Range::cursor/put_cursor/...) difftested 200k cases: matches upstream.
- V `search::find_nth_char` (no panic; = n-th match forward from pos / backward from pos-1, None if n=0, pos>len, or too few), char matcher impl
- O (in progress) match_brackets plain-text fns, surround plain-text fns, textobject word/paragraph/pair, movement word + paragraph + horizontal/vertical moves
- O (tree-sitter, stub for now) goto_treesitter_object, find_parent_start, move_parent_node_end, textobject_treesitter,
  find_matching_bracket, find_matching_bracket_fuzzy, find_pair, as_close_pair, as_open_pair, find_pair_end, as_char,
  find_nth_closest_pairs_ts, all 8 of object.rs; plus the `Some(syntax)` paths of surround/textobject pair fns
### Editing helpers (thread "Verify Helix editing helpers", started 2026-10-24)
history.rs, auto_pairs.rs, comment.rs, indent.rs, increment/*, text_annotations.rs, doc_formatter.rs. Work in /mnt/project-files/helix-verify/helpers/<module>/.
- O all (in progress)

### All other helix-core modules: O
command_line.rs 40, movement.rs 29, indent.rs 27, graphemes.rs 26, text_annotations.rs 24,
history.rs 22, auto_pairs.rs 18, snippets/* 52, match_brackets.rs 15, line_ending.rs 15, uri 9,
textobject 8, surround 8, object 8, comment 7, increment/* 9, case_conversion 6, diff 5, config 5, chars 5,
search 4, editor_config 4, fuzzy 3, diagnostic 3, rope_reader 2, wrap 1, completion 1, syntax/* ~100 (tree-sitter).

## Observations (not reported upstream)
- `ChangeSet::new(doc).invert(doc)` (empty ops, len n>0) gives a set with len 0 that `ChangeSet::apply` refuses.
  Harmless via `Transaction::apply`, which skips empty sets. Counts as needing a verified fix.
- `compose` panics (unreachable!) if an input has a zero-length op. Upstream builders never create one (proved: builders keep NoZero).
- `Transaction::delete` silently drops a range that starts before an earlier range ends but also ends before it,
  which only happens when ranges are not sorted by start. Callers pass sorted selections. (Proved: sorted ⇒ exact union delete.)

## Tool plan for the whole of Helix (Yerin, 2026-10-24: "use different verification tooling... everything must be verified")
- Pure logic (helix-core minus tree-sitter, helix-parsec, pure helix-stdx): Lean via Aeneas, full functional specs.
- Code Aeneas can't translate (trait objects, async, closures-heavy, `dyn`, IO wrappers) in helix-view/term/tui/lsp/dap/vcs/loader/event: Kani (bounded model checking) for panic-freedom, overflow, and stated invariants, with IO/OS stubbed; Verus for any part where a full spec is worth it.
- tree-sitter FFI (helix-core syntax/*): Rust side with Kani against a stubbed parser; C side out of reach unless tree-sitter itself is verified separately (Frama-C, like inih).
- Each finished check goes into the vpipe pipeline so it re-runs on demand.

## Open external assumptions (non-std crates Helix code reaches; see helix-method.md rule)
- ropey 1.6.1 (Rope, RopeSlice: len_chars, slice, insert, remove, chars, ...) — used by transaction.rs, selection.rs, most modules
- smartstring 1.0.1 (Tendril) — transaction.rs
- smallvec 1.15 — selection.rs, transaction.rs
- unicode-segmentation, unicode-width, regex, tree-house — selection.rs, graphemes, movement
- log 0.4 — logging only
