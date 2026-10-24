---
name: pick-verification-target
description: Choose open-source libraries worth formally verifying (widely used, small to medium, no prior verification) and check for prior work. Use when the user asks what to verify next or proposes a library to verify.
---

# Pick a verification target

## Criteria (all three)
1. **Widely used.** Crates: downloads and reverse dependencies on crates.io. C: packaged by
   major distros or vendored by well-known projects. Note the numbers you found.
2. **Small to medium.** Every function in the pinned source must end up verified, so count
   functions, not just lines: under ~5k lines and ~100 functions is a good first target. For a
   big project, pin a self-contained module and treat that as the library (Neovim's base64.c).
   Note anything the tools can't take (SIMD, closures, function pointers): each such function
   needs a patch, model or other tool before the library can be finished.
3. **No public verification attempt.** Search: the library name with "verified", "formal
   verification", "Coq", "Lean", "Isabelle", "Frama-C", "Kani", "Prusti", "Creusot", "Verus";
   Google Scholar; GitHub code search for the crate name in proof repos; the Lean Zulip; the
   tool showcase lists (Aeneas, Frama-C case studies, Kani's verify-rust-std). Note what you checked.

## Admission fit
Only a library that can reach all ten gates (STANDARDS.md) becomes verified. Prefer code
with no `unsafe`, FFI or SIMD, or plan the second tool for those parts up front. Check that a
governing standard or published test vectors exist, so the spec can be checked against them.

## Tool fit
- Rust: Aeneas + Lean. Best on pure, loop-and-array code without trait objects, closures in
  hot paths, or heavy std use. Run `vkit run <lib> --extract-only` early as a feasibility check.
- C: CBMC first, then Frama-C WP. Best on buffer and parsing code with clear contracts.
- Other languages: propose a tool template in an issue first.

## Good first properties
Encoder/decoder round trip; matches a simple reference implementation; no panics/overflow on
any input; no out-of-bounds access; parser accepts exactly the documented grammar.

## Output
For each candidate: name, pinned version, usage numbers, lines and function count, prior-work
search summary, proposed tool, 2-5 candidate properties, and the main risk. Recommend one.
Check `libraries/` and open issues/PRs so you don't duplicate someone's work, and
suggest opening a "Submit a library" issue to claim it.
