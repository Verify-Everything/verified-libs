# smallvec 1.15.2 (Helix + ropey dependency)

Status: in progress. Entry folder: /mnt/project-files/smallvec-verify/ (SCOPE.md lists what Helix uses).

## Method
- Kani 0.68 on the real code (features: write). kani/proofs.rs, run one harness at a time with
  kani/krun.sh (Z3=1 uses CBMC's SMT back end with z3). Never run two CBMC jobs at once here.
- Lengths and capacities symbolic up to 2^30; contents arbitrary; "every index" checked at an
  arbitrary index. Element type E = two u64 (like helix Range), inline sizes 1 and 4.
- Hard harnesses are split by case (inline/spilled, room/full) and by assertion group (p1..p3).
- Growth: grow_spec proves reserve_one_unchecked (4 cases). The full-vector insert harnesses
  use grow_model, a stand-in with the abstract result grow_spec proves (same length, elements,
  capacity next_power_of_two(len+1), spilled).
- A must-fail control harness (remove_c*::spilled_control_must_fail) checks the z3 back end
  finds counterexamples.

## Results (2026-10-27)
- Proved: observers, new/default, with_capacity, push (v1 both, v4 inline), pop (all 4), remove
  inline (v1, v4), remove spilled p1 (both) and p2/p3 for [E;4], remove_c1 spilled p2, insert
  with room (inline both; spilled: all c4 parts, c1 p2/p3), grow (4), insert full via grow_model
  (all c1 parts; c4 inline all, spilled p1), panic harnesses (insert, remove).
- Open (solver runs out of memory or time): remove_c1 spilled p3, insert_c1 spilled_room p1,
  insert_fullm_c4 spilled p2/p3, push_v4 spilled.
- Not started: truncate, extend_from_slice, insert_from_slice, from_vec, from_slice,
  shrink_to_fit, clone, eq, Drop with a drop-tracking type, IntoIter, dedup_by, retain_mut,
  Extend/FromIterator; element types u8 and Arc<Node>.

## Tool notes
- CaDiCaL (default) may run out of memory where minisat proves in seconds; try minisat, kissat.
- z3 back end: CBMC crashes (status 6, `map::at`) on the real growth path; can end in
  Status: ERROR after long runs (treated as not proved). cvc5 back end crashes.

### 2026-10-27: fixed-buffer experiment (failed)
- Tried giving heap vectors one fixed 2^30-element buffer instead of a symbolic-size allocation.
- CBMC stops with status 6 in both back ends: SAT says "array too large for flattening", z3 crashes with map::at.
- The trick is turned off in proofs.rs. The heap element-content parts listed above stay open.

### 2026-10-27: IntoIter proved; dedup_by blocked
- Proved (Kani, minisat, all < 10 s): into_iter (4), next and next_back from any iterator state (8). Control harness fails as it should.
- IntoIter's Drop is not yet proved (it is a loop).
- dedup_by with a loop contract: CBMC stops with status 6 in both back ends (SAT: "array too large for flattening" on the heap buffer havoc; z3: crash). Inline case fails because the havoc of the inline array also havocs the SmallVec fields.
- Conclusion: Kani on this machine cannot do loops that write heap elements with symbolic length. dedup_by, retain_mut, extend, clone and IntoIter drop need another tool.

### 2026-11-02: loops done with Kani steps + Lean
- Decision (Yerin said full speed; card closed as "prove them in another tool"): loops are proved in two pieces. Kani proves one iteration on the real code (loop body moved unchanged into a function in the proof copy). Lean proves the loop of those steps meets the spec. Bounded Kani checks compare the moved bodies with upstream.
- Proved: dedup_by (inline + any heap buffer, all branches), retain/retain_mut (inline + heap, all branches), extend fill step + SetLenOnDrop + reserve (+ overflow panic) + triple_mut, IntoIter drop, PartialEq, Drop. Lean: Dedup.lean, Retain.lean, Extend.lean, IntoIterDrop.lean (propext + Quot.sound only, each with a concrete instance).
- Kani trick: a heap step that runs out of memory on a SmallVec-wrapped buffer proved in 8 min on a raw Vec buffer (dedup_step takes only a pointer).
- Still open: memmove element parts on heap (insert/remove/insert_from_slice spilled p1-p3, push_v4 spilled), drop-tracking element type, real element types (helix Range, u8, Arc<Node>), Debug. See smallvec-verify/CLAIM.md.
