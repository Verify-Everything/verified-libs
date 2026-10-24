import SemverModel.Proofs.RefineParse
import SemverModel.Proofs.RefinePrint
/-! Refinement for `identifier`, `parse_prerelease`, `parse_build` and `parse_version`. -/
open Aeneas Aeneas.Std Result ControlFlow
open semver_model SemverSpec

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace SemverProofs

/-! ## Bounds on what the mirrors return -/

theorem numLoop_le (s : List U8) (st : Nat) (pos : Position) (len v a e : Nat)
    (h : numLoop s st pos len v = .Ok (a, e)) (hb : st + len ≤ s.length) : e ≤ s.length := by
  revert h hb
  fun_induction numLoop s st pos len v <;> intro h hb <;> simp_all <;> (try split_ifs at h) <;> (try simp_all) <;> omega

theorem dotM_ok (s : List U8) (st : Nat) (pos : Position) (e : Nat) (h : dotM s st pos = .Ok e) :
    e = st + 1 ∧ st < s.length := by
  unfold dotM at h; split_ifs at h; simp_all

theorem identLoop_bounds (s : List U8) (st : Nat) (isPre : Bool) (pos : Position) (acc seg : Nat) (nd : Bool)
    (e : Nat) (h : identLoop s st isPre pos acc seg nd = .Ok e) (hb : st + acc + seg ≤ s.length) :
    st ≤ e ∧ e ≤ s.length := by
  revert h hb
  fun_induction identLoop s st isPre pos acc seg nd <;> intro h hb <;> simp_all <;> (try split_ifs at h) <;> (try simp_all) <;> omega

theorem spec_exists {α : Type} {x : Result α} {P : α → Prop} (h : x ⦃ P ⦄) : ∃ r, x = ok r ∧ P r := by
  cases x <;> simp_all [WP.spec_ok]

theorem identifier_spec0 (s : Slice U8) (st : Usize) (isPre : Bool) (h : st.val ≤ s.length) :
    identifier s st isPre ⦃ r => resMap (fun e => e.val) r = identM s.val st.val isPre ⦄ := by
  unfold identifier identM
  cases isPre <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_tc_ok] <;> step*

@[step]
theorem identifier_spec (s : Slice U8) (st : Usize) (isPre : Bool) (h : st.val ≤ s.length) :
    identifier s st isPre ⦃ r => identM s.val st.val isPre = resMap (fun e => e.val) r ∧
      ∀ e, r = .Ok e → st.val ≤ e.val ∧ e.val ≤ s.length ⦄ := by
  obtain ⟨r, hr, hp⟩ := spec_exists (identifier_spec0 s st isPre h)
  rw [hr]; simp only [WP.spec_ok]; refine ⟨hp.symm, ?_⟩
  rintro e rfl
  exact identLoop_bounds _ _ _ _ _ _ _ _ (by simpa [identM] using hp.symm) (by simpa using h)

@[step]
theorem numeric_identifier_spec' (s : Slice U8) (st : Usize) (pos : Position) (h : st.val ≤ s.length) :
    numeric_identifier s st pos ⦃ r => numM s.val st.val pos = resMap (fun p => (p.1.val, p.2.val)) r ∧
      ∀ p, r = .Ok p → p.2.val ≤ s.length ⦄ := by
  obtain ⟨r, hr, hp⟩ := spec_exists (numeric_identifier_spec s st pos h)
  rw [hr]; simp only [WP.spec_ok]; refine ⟨hp.symm, ?_⟩
  rintro p rfl
  exact numLoop_le _ _ _ _ _ _ _ (by simpa [numM] using hp.symm) (by simpa using h)

@[step]
theorem dot_spec' (s : Slice U8) (st : Usize) (pos : Position) :
    dot s st pos ⦃ r => dotM s.val st.val pos = resMap (fun e => e.val) r ∧
      ∀ e, r = .Ok e → e.val = st.val + 1 ∧ st.val < s.length ⦄ := by
  obtain ⟨r, hr, hp⟩ := spec_exists (dot_spec s st pos)
  rw [hr]; simp only [WP.spec_ok]; refine ⟨hp.symm, ?_⟩
  rintro e rfl
  exact dotM_ok _ _ _ _ (by simpa using hp.symm)

/-- Mirror of `Prerelease::new` / `BuildMetadata::new` (`isPre` picks which). -/
def identWholeM (s : List U8) (isPre : Bool) : Res (List U8) :=
  match identM s 0 isPre with
  | .Err e => .Err e
  | .Ok e => if e = s.length then .Ok (sub s 0 e)
             else .Err (.UnexpectedCharAfter (if isPre then .Pre else .Build))

@[step]
theorem parse_prerelease_spec (s : Slice U8) :
    parse_prerelease s ⦃ r => resMap (fun p => p.ident.val) r = identWholeM s.val true ⦄ := by
  unfold parse_prerelease identWholeM
  obtain ⟨r, hr, hp⟩ := spec_exists (identifier_spec0 s 0#usize true (by simp))
  rw [hr]
  have h0 : (0#usize).val = 0 := rfl
  rcases r with e | e <;> simp only [resMap, h0] at hp <;> rw [← hp] <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from]
  have hsl : s.length = s.val.length := rfl
  have := identLoop_bounds s.val 0 true .Pre 0 0 false e.val (by simpa [identM] using hp.symm) (by simp)
  split
  · step*
    simp_all
  · simp_all

@[step]
theorem parse_build_spec (s : Slice U8) :
    parse_build s ⦃ r => resMap (fun p => p.ident.val) r = identWholeM s.val false ⦄ := by
  unfold parse_build identWholeM
  obtain ⟨r, hr, hp⟩ := spec_exists (identifier_spec0 s 0#usize false (by simp))
  rw [hr]
  have h0 : (0#usize).val = 0 := rfl
  rcases r with e | e <;> simp only [resMap, h0] at hp <;> rw [← hp] <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from]
  have hsl : s.length = s.val.length := rfl
  have := identLoop_bounds s.val 0 false .Build 0 0 false e.val (by simpa [identM] using hp.symm) (by simp)
  split
  · step*
    simp_all
  · simp_all

/-! ## `parse_version` -/

theorem usize_eq_len {α : Type} (a : Usize) (s : Slice α) : (a = s.len) ↔ a.val = s.val.length := by
  rw [UScalar.eq_equiv, Slice.len_val]

theorem usize_eq_iff (a b : Usize) : (a = b) ↔ a.val = b.val := UScalar.eq_equiv a b

theorem usize_lt_len {α : Type} (a : Usize) (s : Slice α) : (a < s.len) ↔ a.val < s.val.length := by
  rw [UScalar.lt_equiv, Slice.len_val]

theorem u8_eq_iff (a b : U8) : (a = b) ↔ a.val = b.val := UScalar.eq_equiv a b

theorem branch_ok_eq {T : Type} (v : T) :
    core.result.Result.Insts.CoreOpsTry.branch (E := ErrorKind) (.Ok v) = ok (.Continue v) := rfl
theorem branch_err_eq {T : Type} (e : ErrorKind) :
    core.result.Result.Insts.CoreOpsTry.branch (T := T) (.Err e) = ok (.Break (.Err e)) := rfl
theorem residual_eq {T : Type} (e : ErrorKind) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T
      (core.convert.FromSame ErrorKind) (.Err e) = ok (.Err e) := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from]

@[step]
theorem branch_spec' {T : Type} (r : core.result.Result T ErrorKind) :
    core.result.Result.Insts.CoreOpsTry.branch r ⦃ cf =>
      (∀ v, cf = .Continue v → r = .Ok v) ∧ (∀ res, cf = .Break res → ∃ e, r = .Err e ∧ res = .Err e) ⦄ := by
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch, WP.spec_ok]

theorem getElem_bang {l : List U8} {i : Nat} (h : i < l.length) : l[i] = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem vec_new_val : (alloc.vec.Vec.new U8).val = [] := rfl

set_option hygiene false in
macro "pv_close" : tactic => `(tactic| (
  (try simp only [getElem_bang] at *) <;>
  simp_all [usize_eq_len, usize_lt_len, u8_eq_iff, vec_new_val, Version.toP,
    resMap, identM] <;>
  (try omega) <;> (try scalar_tac)))

set_option maxHeartbeats 4000000 in
theorem parse_version_spec (s : Slice U8) :
    parse_version s ⦃ r => resMap Version.toP r = parseM s.val ⦄ := by
  have hsl : s.length = s.val.length := rfl
  have h0 : (0#usize).val = 0 := rfl
  unfold parse_version parseM
  by_cases hz : s.val.length = 0
  · simp [hz, slice_len_eq_zero, WP.spec_ok]
  have hne : ¬ s.len = 0#usize := by rw [slice_len_eq_zero]; exact hz
  dsimp only
  rw [if_neg hne, if_neg hz]
  step*
  all_goals (try (obtain ⟨major, k⟩ := val; step*))
  all_goals (try (obtain ⟨minor, k1⟩ := val2; step*))
  all_goals (try (obtain ⟨patch, k2⟩ := val4; step*))
  all_goals (try clear hsl)
  all_goals (try clear h0)
  all_goals (try clear hne)
  all_goals pv_close

end SemverProofs
