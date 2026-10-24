# How Helix functions are verified (read before starting a Helix module)

Status/tracker: verification-notes/helix.md (update your module's lines there; re-read before writing, last write wins).
Worked example: /mnt/project-files/helix-verify/ (ChangeSet: model crate, difftest, Lean proofs).

## Toolchain
- `bash /mnt/project-files/pipeline/bootstrap.sh lean` (Aeneas fdebf20, Rust nightly-2026-09-17, Lean 4.35.0, zstd).
- PATH: `export PATH=$HOME/.vpipe/aeneas:$HOME/.elan/bin:$HOME/.vpipe/bin:$PATH`
- Mathlib cache: verification-notes/cache/aeneas-fdebf20-mathlib-v4.35.0-packages.tar.zst -> unpack into <lean>/.lake/packages
  (`tar --use-compress-program=zstd -xf ...`). /mnt/project-files is noexec: copy work to your home dir to build.
- Upstream: clone github.com/helix-editor/helix at ba40e547426b0f9896c8bdc699a4ab11f2b37dbc (read-only).

## Standard (Yerin approved, 2026-10-24): verified-libs admission standards
Read it: https://claude.ai/artifact/1tqQsrMgXckaNZQJVXPWvp . What changes for Helix:
- Only full functional correctness ON THE REAL UPSTREAM CODE (pinned commit, byte for byte) counts as "verified".
  A model crate checked by differential tests is label `tested`, never `verified`, however many cases pass.
  A model counts only with a proof that model and real code behave the same, or if a published fork replaces the code with it.
- Every function the library reaches, incl. derived/impl'd traits (Debug, Clone, PartialEq, Default), every feature, any input size.
  No size caps; if a proof needs a bound like "doc length + new length fits in usize", list it in CLAIM.md and say why it can't fail.
- Specs written and reviewed before proofs; spec must not be vacuous (planted bugs must break the proof).
- Allowed in Lean: only propext, Classical.choice, Quot.sound in `#print axioms`, plus std-library models in FunsExternal that are
  each differential-tested against real std. Forbidden: sorry, admit, new axioms, native_decide, bv_decide, implemented_by, @[extern].
  Aeneas leaves `sorry` bodies for items it fails on and `axiom`s for unmodelled externals: each must be replaced by a real
  definition (or proved model) before a theorem that reaches it counts.
- Label each function: full-correctness / safety-contracts / no-ub / bounded / tested. Record in functions.toml.
- Bugs: report fixes as "proved fix" only when the fix is proved on the real (patched) code.

## Rule for third-party dependencies (all Helix threads; Yerin decided 2026-10-24: the used parts of ropey, smartstring, smallvec get verified as separate entries)
ropey, smartstring, smallvec, unicode-segmentation, unicode-width, regex, tree-house/tree-sitter, log, url, nucleo, imara-diff,
toml/serde, globset, etc. are NOT std. The same decision applies to each: it becomes its own verified-libs entry.
- Model each one you reach as a small Lean definition (or a parameter with a stated spec), never as a bare `axiom` with no spec.
- List every one in your STATUS.md and in helix.md under "Open external assumptions": crate + version, the functions used,
  the exact behaviour assumed, and the differential test that checks the model against the real crate.
- A function whose proof uses such a model is labelled at best `full-correctness (assuming <crate>)` in functions.toml and
  does NOT count for admission. Helix stays `candidate` until each assumed crate is verified as its own entry
  (or Yerin decides otherwise; check helix.md for the decision).
- `log` macros: treat logging as having no effect on results; still list it.

## Method (from 2026-10-24 on)
1. Extract the REAL helix-core code: scratch copy of upstream, then in helix-core
   `charon cargo --preset=aeneas --start-from 'helix_core::<module>' --dest-file real.llbc`, then
   `aeneas -backend lean real.llbc -dest . -split-files`. Do not edit upstream source. (Tried on transaction.rs:
   it translates; ~10 items come out as `sorry` (iterator adapters, closures, SmallVec) and ~100 externals need models.)
2. Externals: std items (iterators, Option, Vec, str::chars, slice ops) -> write the model in FunsExternal.lean, and add a
   differential test of that model against real std. Third-party crates (ropey Rope/RopeSlice, smartstring Tendril, smallvec,
   log, unicode-segmentation) are NOT std: they are open assumptions until verified on their own; list them in the tracker.
3. Where Aeneas can't translate an item (sorry body), first try a supported Charon/Aeneas option; otherwise use a second tool
   on the real code (Verus or Kani with unbounded proofs / loop contracts) and link the proofs. Don't replace it with a model.
4. Existing model-crate proofs (helix-verify/model, motion/, selection/, helpers/...) are reusable as list-level specs and proof
   scripts, but count only after a model-to-real equivalence proof or a re-proof on the real extraction. Mark them `tested`
   in the tracker until then.
5. Differential tests stay: they are gate 8 (cross-check of the translation) and catch spec mistakes early.
6. Lean: list-level spec + proof that the extracted real code meets it (no panic + functional result), `#print axioms` clean.

## Real-code extraction tricks (from the transaction.rs and parsers threads, 2026-10-24)
- Don't mark core/alloc/std opaque (crashes Aeneas on builtin types).
- `--exclude 'core::str::pattern'` (Aeneas crashes on the Pattern GAT). str::find/contains/split then show up as
  `sorry /- Could not find: trait_impl_id -/`: replace them by script with a hand-defined Pattern stand-in, and list it as a translation patch.
- Some setups need the copy's rust-toolchain.toml removed; transaction.rs worked with helix-verify/model/rust-toolchain.toml copied in.
- Aeneas `Str` = `Slice U8` with no UTF-8 invariant, so specs need a UTF-8 precondition.
- Aeneas's `Iterator` structure only has next/step_by/enumerate/take. Generated instances also set size_hint/count/map/...:
  helix-verify/real/tools/postprocess.py drops the unused fields. Real code that calls `Inst.size_hint` (from_changes, delete)
  needs a `size_hint` field: we vendor Aeneas with one field added (default `(0, None)`, as in Rust). List it as a library patch.
- A local variable named like a module (`selection`) shadows `selection.Selection.iter`: fully qualify (`helix_core.selection...`) in postprocess.
- Known blockers: fn-pointer fields ("Arrow types"), early return inside a loop or closure, str::strip_suffix, Box AsRef,
  closures taking `&mut` pairs (Selection::normalize), SmallVec. These need another tool or an Aeneas fix.

## Lean lessons (Aeneas fdebf20 / Lean 4.35)
- `lake env lean F.lean` does not rebuild deps: `lake build <Module>` after re-extraction or edits.
- Use `step*?` to get an explicit `let* ⟨ x, x_post, … ⟩ ← spec` script; step*-generated names are inaccessible.
- If a `let*` precondition was discharged automatically, a following `· omega` lands on the wrong goal. Check before adding bullets.
- omega sees `v.length` (Vec/Slice abbrev) and `v.val.length` as different atoms: add `have : v.length = v.val.length := rfl`.
- Aeneas consts (e.g. NONE/RETAIN) are irreducible: prove a `kind_consts` lemma and simp with it.
- Inside `first | …` use `fail_if_no_progress`, not `progress`.
- `let (a, b) ← do …` blocks: `simp only [bind_tc_eq, Std.bind_assoc]` before step*. A goal with `let (x,_) := (a,b)` that dsimp
  won't touch can be restated with `show`.
- Loops: `loop.spec_decr_nat measure inv` with `unfold <f>_loop; apply loop.spec_decr_nat …; rintro ⟨…⟩ hinv; unfold <f>_loop.body`.
