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
- position.rs: MODEL-PROVED all 17 functions + derives except Debug (23 theorems, std axioms; difftest 120k-240k cases each). Bridge to real code in progress (helix-verify/position/real/). O: Debug, `unicode-lines`, size caps to classify. Details: helix-verify/position/STATUS.md.
- position.rs findings (not filed): pos_at_coords(limit=false) panics when row > len_lines; tab_width = 0 divides by zero; softwrapped_dimensions truncates with `as u16` (70000 chars -> 4464); Position Sub is componentwise ((1,0)-(0,1) panics in debug, wraps in release); visual_offset_from_anchor `anchor_line + max_rows` overflows for max_rows = usize::MAX. doc_formatter (other thread): loops forever when the wrap indicator is wider than viewport minus retained indent (e.g. viewport 12, indicator "->->->->-> ").
### Parsers/utilities thread ("Verify Helix parsers": command_line, snippets/*, uri, fuzzy, diff, editor_config, config, diagnostic)
Work dirs: helix-verify/utils-real/ (REAL-CODE proofs, see README), helix-verify/utils/ (model, now only `tested`),
helix-verify/command_line/, snippets_parse/, snippets_render/ (helper agents; each has STATUS.md).
All real-code theorems: axioms only propext, Classical.choice, Quot.sound; no sorry.
- BUG editor_config.rs `is_glob_relative`: `|close| idx + close` should be `open + close`, and `source[..open]` should be
  `source[idx..open]`. Wrong answers: "a[/]", "ab[c][d/]", "[a/]b[c]" return true (should be false). Panic: glob "éé[ab]"
  (section header `[éé[ab]]`) slices inside 'é', so reading such an .editorconfig crashes Helix. Confirmed by running upstream.
- V (real code, fork fix) `is_glob_relative`: `fix_is_glob_relative_spec`: no panic on any input, result = EditorConfig rule.
- V (real code) `EditorConfig::from_pairs`, default and unicode-lines builds: `from_pairs_spec` = exact output for every map.
- Gate 8 (editor_config): extracted Lean run against compiled upstream/fork Rust, 240k cases, 0 mismatches
  (utils-real/gate8/run.sh; planted differences are caught). Std models difftested 150k cases, 0 mismatches.
- command_line.rs (helper, command_line/STATUS.md): 27 of 45 V on real code, no bugs. 17 D (Aeneas crashes on
  str::pattern, dyn traits, lifetime constraints): split, Flag/ExpansionKind consts, Display, parse_unquoted, parse_quoted,
  parse_percent_token, parse_quoted_balanced, Iterator::next, read_token, parse, push, first/get/get_flag, Index, IntoIterator
  for &Args. Its std contracts (HashMap assoc list, str eq) still need gate-7 difftests.
- tested only (model proofs + difftests): uri.rs, diagnostic.rs, config.rs, fuzzy.rs; editor_config Ini::from_str, find;
  diff.rs. snippets: see helper STATUS files (bugs B1-B6 in snippets_render).
- Aeneas blockers on real code: str::pattern (crash), fmt (Formatter opaque, so no Display/Debug), fuzzy fn-pointer field,
  config::user_lang_loader early return in closure loop, str::strip_suffix closure and Box AsRef (Ini::from_str, find),
  diff FnMut closures, diagnostic serde derives.
### movement.rs, textobject.rs, match_brackets.rs, surround.rs, object.rs, search.rs (72 fns) — thread "Verify Helix movement and objects"
Work: /mnt/project-files/helix-verify/motion/ (model crate, Lean project HelixMotion, difftest/run_difftest.sh, real-probe/).
Under the admission standards (2026-10-24) NOTHING here counts as verified yet: all proofs below are about a model crate (label M = model proved in Lean + difftested 200k, no model-to-code proof). Every function is O for admission.
Text model: RopeSlice = list of `Ch` (code point + Unicode facts as data). Lines: default build (`unicode-lines` off).
- M search: find_nth_char
- M movement: move_horizontally, word_move + 12 wrappers, range_to_target, is_word/long_word/sub_word_boundary, reached_target, skip_while, backwards_skip_while, move_prev/next_paragraph, move_vertically, move_vertically_visual (soft_wrap=false, no inline annotations only; soft wrap open)
- M textobject: find_word_boundary, textobject_word, textobject_paragraph, Display for TextObject
- M match_brackets: BRACKETS, PAIRS, get_pair, is_{open,close,valid}_{bracket,pair}, find_matching_bracket_plaintext
- M surround (syntax=None paths): find_nth_open_pair, find_nth_close_pair, find_nth_pairs_pos, find_nth_closest_pairs_plain, find_nth_closest_pairs_pos, get_surround_pos, Display for Error
- M textobject: textobject_pair_surround, _closest, _impl (syntax=None)
- in progress (model): tree-sitter fns and Some(syntax) paths via an abstract tree model
- Real-code probe (Aeneas fdebf20 on unmodified helix-core, deps ropey/unicode-segmentation/tree-house opaque): only find_nth_char, skip_while, as_char translate with no sorry anywhere. The rest hit Aeneas limits: non-ASCII char literals (most common), closures/arrow types, lifetime constraints, continue-to-outer-loop. A worker is extending Aeneas (char literals first).
- Likely bug (not reported, needs a verified fix): find_nth_closest_pairs_plain shifts close positions by one when the range starts at 0 (`close_pos = pos.saturating_sub(1)`). On ")(" with cursor 0 it returns (1,1); so get_surround_pos(None) can return a duplicate position and surround delete/replace build overlapping changes. Proved on the model (closestPlain_oddity) and confirmed on upstream by difftest.
- Odd behaviour seen (not reported): `miW`/`maW` with cursor on whitespace or \n right after a WORD selects that WORD (`miw` selects nothing); count=0 paragraph motions can move the wrong way (callers pass >=1); backwards_skip_while doc says "saturating" but returns None when all chars match.
### history.rs, auto_pairs.rs, comment.rs, indent.rs, increment/*, text_annotations.rs, doc_formatter.rs — thread "Verify Helix editing helpers"
Work: /mnt/project-files/helix-verify/helpers/ (indent_ts/ = tree-sitter part of indent.rs: model, difftest, Lean project IndentTS).
Under the admission standards NOTHING here counts as verified yet (model proofs only, label M = model proved in Lean, no sorry, + difftest).
- indent.rs (tree-sitter part) difftest vs real upstream: 106 files, 10 languages, 2120 positions incl. 45 injections, all agree.
- M indent.rs text helpers (line/byte/char conversions, whitespace, tab width, indent_level_for_line), injection_base_level, get_scopes, parent walk, has_header, last_preceding_child, deepest_last, opaque_hit / is_opaque_interior / any_opaque_hit, candidate_body_for_new_line, extend_nodes, is_outdent_token_at upward walk, account_node capture scan. In progress: account_node, containment_accounting, query side (IndentQuery::new, are_satisfied, process_match, query_indents), treesitter_indent_for_pos.
- BUG (confirmed on real upstream, not filed): injection_base_level panics (ropey slice.rs:515) when Enter is pressed inside an injection on the last line with no trailing newline, e.g. `<script>foo();</script>` at EOF in HTML. Fix `(bl + 1).min(total - 1)` proved on the model; patch helpers/indent_ts/patches/, issue draft helpers/indent_ts/issues/.
- history.rs, increment/*, auto_pairs.rs, comment.rs, indent.rs (non-tree-sitter), text_annotations.rs, doc_formatter.rs: workers in progress; doc_formatter infinite-loop finding is listed under position.rs above.
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
Decision (Yerin, 2026-10-24): verify the used parts of ropey, smartstring and smallvec as separate entries on their real code. Helix stays candidate until then.
- ropey 1.6.1 (Rope, RopeSlice: len_chars, slice, insert, remove, chars, ...) — used by transaction.rs, selection.rs, most modules
- smartstring 1.0.1 (Tendril) — transaction.rs
- smallvec 1.15 — selection.rs, transaction.rs
- unicode-segmentation, unicode-width, regex, tree-house — selection.rs, graphemes, movement
- unicode-general-category 1.1, str_indices, textwrap 0.16.2 — chars.rs, graphemes.rs, wrap.rs (text helpers thread)
- log 0.4 — logging only
- Parsers thread (functions used):
  - helix_stdx (Helix's own crate, not third-party: Url is a String newtype; Url::scheme/from_file_path/to_file_path/clone,
    path::normalize) — uri.rs. Extracts with Charon `--include helix_stdx::uri`; proved together with uri.rs.
  - percent_encoding (percent_encode, percent_decode, NON_ALPHANUMERIC, AsciiSet::remove) — via helix_stdx::uri
  - dunce::simplified — via helix_stdx::path::normalize
  - globset: GlobBuilder::new/literal_separator/backslash_escape/empty_alternates/build, Glob::compile_matcher, GlobMatcher::is_match — editor_config.rs
  - encoding_rs: UTF_8, UTF_16LE, UTF_16BE, WINDOWS_1252 statics (modelled by name only) — editor_config.rs
  - nucleo (Matcher, Config, pattern matching) — fuzzy.rs; imara-diff (Diff, intern) — diff.rs
  - toml + serde (Deserialize derives, from_str) — config.rs, diagnostic.rs, snippets; helix_loader (config paths) — config.rs
