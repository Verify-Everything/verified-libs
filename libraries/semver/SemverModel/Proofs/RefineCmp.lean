import SemverModel.Code.Funs
import SemverModel.Spec.Mirror
/-! Refinement: the Aeneas-generated comparison functions equal the pure mirrors. -/
open Aeneas Aeneas.Std Result ControlFlow
open semver_model SemverSpec

namespace SemverProofs

@[step]
theorem is_digit_spec (b : U8) : is_digit b ⦃ r => r = isDig b ⦄ := by
  unfold is_digit isDig
  split <;> simp_all

@[step]
theorem segment_end_spec (s : Slice Std.U8) (i : Std.Usize) (h : i.val ≤ s.length) :
    segment_end s i ⦃ r => r.val = segEnd s.val i.val ⦄ := by
  unfold segment_end segment_end_loop
  apply loop.spec_decr_nat (fun x => s.length - x.val)
    (fun x => x.val ≤ s.length ∧ segEnd s.val x.val = segEnd s.val i.val)
  · intro x ⟨h1, h2⟩
    unfold segment_end_loop.body
    step*
    · have : x.val < s.val.length := by scalar_tac
      rw [← h2, segEnd]; simp_all
    · have : x.val < s.val.length := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← h2, segEnd.eq_1 _ x.val]; simp_all
    · have : ¬ x.val < s.val.length := by scalar_tac
      rw [← h2, segEnd]; simp_all
  · exact ⟨h, rfl⟩

@[step]
theorem all_digits_spec (s : Slice Std.U8) (a e : Std.Usize) (h : e.val ≤ s.length) :
    all_digits s a e ⦃ r => r = allDigits s.val a.val e.val ⦄ := by
  unfold all_digits all_digits_loop
  apply loop.spec_decr_nat (fun x => e.val - x.val)
    (fun x => allDigits s.val x.val e.val = allDigits s.val a.val e.val)
  · intro x h2
    unfold all_digits_loop.body
    step*
    · have : x.val < e.val := by scalar_tac
      have : x.val < s.val.length := by scalar_tac
      refine ⟨?_, by scalar_tac⟩
      rw [← h2, allDigits.eq_1 _ x.val]; simp_all
    · have : x.val < e.val := by scalar_tac
      have : x.val < s.val.length := by scalar_tac
      rw [← h2, allDigits]; simp_all
    · have : ¬ x.val < e.val := by scalar_tac
      rw [← h2, allDigits]; simp_all
  · rfl

@[step]
theorem cmp_bytes_spec (s : Slice Std.U8) (a ae : Std.Usize) (t : Slice Std.U8) (b be : Std.Usize)
    (hs : ae.val ≤ s.length) (ht : be.val ≤ t.length) :
    cmp_bytes s a ae t b be ⦃ r => r = cmpBytes s.val a.val ae.val t.val b.val be.val ⦄ := by
  unfold cmp_bytes cmp_bytes_loop
  apply loop.spec_decr_nat (fun x => ae.val - x.1.val)
    (fun x => cmpBytes s.val x.1.val ae.val t.val x.2.val be.val = cmpBytes s.val a.val ae.val t.val b.val be.val)
  · intro ⟨p, q⟩ h2
    unfold cmp_bytes_loop.body
    step*
    · rw [← h2, cmpBytes_step (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)]
      simp_all
    · rw [← h2, cmpBytes_step (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)]
      simp_all
    · rw [← h2, cmpBytes_step (a := p.val) (b := q.val) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)]
      refine ⟨?_, by scalar_tac⟩
      have : x.val = y.val := by scalar_tac
      simp_all
    · rw [← h2, cmpBytes_stop (by scalar_tac)]; split_ifs <;> first | rfl | (exfalso; scalar_tac)
    · rw [← h2, cmpBytes_stop (by scalar_tac)]; split_ifs <;> first | rfl | (exfalso; scalar_tac)
    · rw [← h2, cmpBytes_stop (by scalar_tac)]; split_ifs <;> first | rfl | (exfalso; scalar_tac)
  · rfl

@[step]
theorem cmp_usize_spec (a b : Std.Usize) : cmp_usize a b ⦃ r => r = cmpNat a.val b.val ⦄ := by
  unfold cmp_usize cmpNat
  split_ifs <;> simp_all

@[step]
theorem cmp_u64_spec (a b : Std.U64) : cmp_u64 a b ⦃ r => r = cmpNat a.val b.val ⦄ := by
  unfold cmp_u64 cmpNat
  split_ifs <;> simp_all

@[step]
theorem skip_zeros_spec (s : Slice Std.U8) (a e : Std.Usize) (h : e.val ≤ s.length) :
    skip_zeros s a e ⦃ r => r.val = skipZeros s.val a.val e.val ⦄ := by
  unfold skip_zeros skip_zeros_loop
  apply loop.spec_decr_nat (fun x => e.val - x.val)
    (fun x => skipZeros s.val x.val e.val = skipZeros s.val a.val e.val)
  · intro p h2
    unfold skip_zeros_loop.body
    step*
    · rw [← h2, skipZeros_step (by scalar_tac) (by scalar_tac)]; simp_all
    · rw [← h2, skipZeros_step (a := p.val) (by scalar_tac) (by scalar_tac)]
      refine ⟨?_, by scalar_tac⟩
      simp_all
    · rw [← h2, skipZeros_stop (by scalar_tac)]
  · rfl

@[step]
theorem pre_segment_cmp_spec (l : Slice Std.U8) (i le : Std.Usize) (r : Slice Std.U8) (j re : Std.Usize)
    (h1 : i.val ≤ le.val) (h2 : le.val ≤ l.length) (h3 : j.val ≤ re.val) (h4 : re.val ≤ r.length) :
    pre_segment_cmp l i le r j re ⦃ o => o = preSegCmp l.val i.val le.val r.val j.val re.val ⦄ := by
  unfold pre_segment_cmp preSegCmp
  step*

@[step]
theorem build_segment_cmp_spec (l : Slice Std.U8) (i le : Std.Usize) (r : Slice Std.U8) (j re : Std.Usize)
    (h1 : i.val ≤ le.val) (h2 : le.val ≤ l.length) (h3 : j.val ≤ re.val) (h4 : re.val ≤ r.length) :
    build_segment_cmp l i le r j re ⦃ o => o = buildSegCmp l.val i.val le.val r.val j.val re.val ⦄ := by
  have := skipZeros_bounds l.val i.val le.val h1
  have := skipZeros_bounds r.val j.val re.val h3
  unfold build_segment_cmp buildSegCmp
  step*
  all_goals (subst_vars; simp_all)

@[step]
theorem cmp_segments_loop_spec (l r : Slice Std.U8) (build : Bool) (i j : Std.Usize) (rdone : Bool)
    (hi : i.val ≤ l.length) (hj : j.val ≤ r.length) :
    cmp_segments_loop l r build i j rdone ⦃ o => o = cmpSegsLoop l.val r.val build i.val j.val rdone ⦄ := by
  unfold cmp_segments_loop
  apply loop.spec_decr_nat (fun x => l.length + 1 - x.1.val)
    (fun x => x.1.val ≤ l.length ∧ x.2.1.val ≤ r.length ∧
      cmpSegsLoop l.val r.val build x.1.val x.2.1.val x.2.2 = cmpSegsLoop l.val r.val build i.val j.val rdone)
  · intro ⟨p, q, rd⟩ ⟨hp, hq, h2⟩
    have := segEnd_bounds l.val p.val hp
    have := segEnd_bounds r.val q.val hq
    rw [cmpSegsLoop_unfold _ _ _ _ _ _ hp] at h2
    simp only at hp hq h2
    unfold cmp_segments_loop.body
    cases build
    · step*
      split
      · step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have : re.val = r.length := by scalar_tac
        have : le.val ≠ l.length := by scalar_tac
        rw [← h2]; subst_vars; (try simp only [eq_comm (a := Ordering.eq)] at *); simp_all
      · step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have : re.val ≠ r.length := by scalar_tac
        have : le.val ≠ l.length := by scalar_tac
        rw [← h2]; subst_vars; (try simp only [eq_comm (a := Ordering.eq)] at *); simp_all
    · step*
      split
      · step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have : re.val = r.length := by scalar_tac
        have : le.val ≠ l.length := by scalar_tac
        rw [← h2]; subst_vars; (try simp only [eq_comm (a := Ordering.eq)] at *); simp_all
      · step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have : re.val ≠ r.length := by scalar_tac
        have : le.val ≠ l.length := by scalar_tac
        rw [← h2]; subst_vars; (try simp only [eq_comm (a := Ordering.eq)] at *); simp_all
  · exact ⟨hi, hj, rfl⟩

@[simp] theorem deref_val {α : Type} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  unfold alloc.vec.Vec.deref; simp

@[simp] theorem slice_len_eq_zero {α : Type} (v : Slice α) : v.len = 0#usize ↔ v.val.length = 0 := by
  constructor
  · intro h; have := Slice.len_val v; simp_all
  · intro h; have := Slice.len_val v; scalar_tac

@[step]
theorem prerelease_cmp_spec (a b : Prerelease) :
    prerelease_cmp a b ⦃ o => o = preCmp a.ident.val b.ident.val ⦄ := by
  unfold prerelease_cmp preCmp cmp_segments
  step*
  all_goals simp_all

@[step]
theorem build_cmp_spec (a b : BuildMetadata) :
    build_cmp a b ⦃ o => o = buildCmp a.ident.val b.ident.val ⦄ := by
  unfold build_cmp buildCmp cmp_segments
  step*
  all_goals simp_all

/-- Pure view of an extracted `Version`. -/
def _root_.semver_model.Version.toP (v : Version) : PVersion :=
  ⟨v.major.val, v.minor.val, v.patch.val, v.pre.ident.val, v.build.ident.val⟩

@[step]
theorem version_cmp_spec (a b : Version) :
    version_cmp a b ⦃ o => o = versionCmp a.toP b.toP ⦄ := by
  unfold version_cmp versionCmp Version.toP
  step*
  all_goals (subst_vars; (try simp only [eq_comm (a := Ordering.eq), eq_comm (a := Ordering.lt), eq_comm (a := Ordering.gt)] at *); simp_all)

end SemverProofs
