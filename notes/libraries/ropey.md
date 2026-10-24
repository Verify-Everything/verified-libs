# ropey 1.6.1 status

Thread: "Verify ropey for Helix". Work: /mnt/project-files/ropey-verify/ (extract/, kani/, lean/ as they appear).
Source: crates.io ropey-1.6.1.crate, sha256 93411e42...93b5 (= Helix Cargo.lock checksum; same files as git tag v1.6.1, d41ee24).
Build Helix uses: `default-features = false, features = ["simd"]` (LF-only lines). helix-core's `unicode-lines` feature turns on
ropey `unicode_lines` (CR and Unicode breaks), so both line modes are in scope.
NOT finished. Nothing is verified yet.

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

## Extraction result (2026-10-24, Aeneas fdebf20)
`bash ropey-verify/extract/extract.sh`. Needed: inner modules opaque, two Debug impls opaque (type/function cycle).
- Rope: all methods translate except `from_reader` (io::Error uses dyn).
- Tree (node.rs, node_children.rs safe part, node_text.rs safe part, text_info, str_utils, crlf): translate, except
  NodeChildren::{search_by, search_char_idx_only, search_char_idx_range, merge_distribute} and Node::assert_integrity.
- RopeSlice: about 25 methods fail (borrow inside the RSEnum enum, "continue to outer loop" in new_with_range):
  new_with_range, new_with_byte_range, slice, get_slice, as_str, len_bytes, chars, chunks, lines, bytes, get_*_at,
  try_chunk_at_byte, utf16 conversions, PartialEq/Ord/Hash/Display. Iterators: Chars/Bytes/Lines/Chunks constructors,
  Chunks/Lines next_impl/prev_impl.
- 150 externals: std (str, String, Arc, Vec, slice, fmt), smallvec, str_indices, and the two unsafe inner modules.

## Plan
1. Unsafe core (node_children::inner = fixed-capacity arrays of Arc<Node>, 14 fns; node_text::inner = NodeSmallString, ~11 fns):
   Kani proofs on the real code that each function matches a Vec/String spec. Capacity is a constant, so a proof for every length up
   to capacity covers every input. These specs become the definitions used in Lean for the opaque inner functions.
2. Arc: modelled as a plain value (make_mut = copy-on-write gives the same observable values). Needs a stated std model + difftest.
3. Safe layer in Lean on the real extraction: tree invariants, then each Rope method's full functional spec on a list-of-chars view.
4. RopeSlice and iterator parts Aeneas can't read: try an Aeneas fix or newer release first; else another tool (Verus download is
   blocked here for now: github release assets 404 without the API; Kani with function contracts is the fallback).
5. str_indices and smallvec: separate entries (str_indices includes SIMD intrinsics).

## Per-function tracker
All O (open). Will be filled per function as proofs land.

## Findings
None yet.
