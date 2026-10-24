import SemverModel.Proofs.RefineCmp
import SemverModel.Spec.ParseMirror
/-! Refinement for the byte-copying and printing functions. -/
open Aeneas Aeneas.Std Result ControlFlow
open semver_model SemverSpec

namespace SemverProofs

theorem sub_succ (l : List U8) (a k : Nat) (h1 : a ≤ k) (h2 : k < l.length) :
    sub l a (k + 1) = sub l a k ++ [l[k]] := by
  unfold sub
  rw [List.take_add_one, List.getElem?_eq_getElem h2, List.drop_append_of_le_length (by simp; omega)]
  simp

theorem sub_self (l : List U8) (a : Nat) : sub l a a = [] := sub_nil (Nat.le_refl a)

@[step]
theorem push_all_loop_spec (out : alloc.vec.Vec U8) (s : Slice U8) (e i : Usize)
    (h1 : i.val ≤ e.val) (h2 : e.val ≤ s.length) (h3 : out.length + (e.val - i.val) ≤ Usize.max) :
    push_all_loop out s e i ⦃ r => r.val = out.val ++ sub s.val i.val e.val ⦄ := by
  unfold push_all_loop
  apply loop.spec_decr_nat (fun x => e.val - x.2.val)
    (fun x => i.val ≤ x.2.val ∧ x.2.val ≤ e.val ∧ x.1.val = out.val ++ sub s.val i.val x.2.val ∧
      x.1.length + (e.val - x.2.val) ≤ out.length + (e.val - i.val))
  · intro ⟨o, k⟩ ⟨hk1, hk2, hk3, hk4⟩
    have hsl : s.length = s.val.length := rfl
    have hol : o.length = o.val.length := rfl
    unfold push_all_loop.body
    simp only at *
    split
    · step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · simp_all [sub_succ s.val i.val k.val (by omega) (by scalar_tac)]
      · simp_all; scalar_tac
    · simp only [WP.spec_ok]
      have : k.val = e.val := by scalar_tac
      simp_all
  · simp [sub_self]; omega

@[step]
theorem push_all_spec (out : alloc.vec.Vec U8) (s : Slice U8) (st e : Usize)
    (h1 : st.val ≤ e.val) (h2 : e.val ≤ s.length) (h3 : out.length + (e.val - st.val) ≤ Usize.max) :
    push_all out s st e ⦃ r => r.val = out.val ++ sub s.val st.val e.val ⦄ := by
  unfold push_all; step*

@[step]
theorem copy_range_spec (s : Slice U8) (st e : Usize) (h1 : st.val ≤ e.val) (h2 : e.val ≤ s.length) :
    copy_range s st e ⦃ r => r.val = sub s.val st.val e.val ⦄ := by
  unfold copy_range
  have : (alloc.vec.Vec.new U8).length + (e.val - st.val) ≤ Usize.max := by
    simp [alloc.vec.Vec.new, alloc.vec.Vec.length]; scalar_tac
  step*

theorem decimal_unfold (n : Nat) : decimal n =
    (if n ≥ 10 then decimal (n / 10) else []) ++ [UScalar.ofNat (48 + n % 10) (by
      have := Nat.mod_lt n (by decide : 10 > 0); scalar_tac)] := by
  rw [decimal]

theorem decimal_length_pos (n : Nat) : 1 ≤ (decimal n).length := by
  rw [decimal_unfold]; simp

theorem digit_eq (n : Nat) (i : U64) (i1 i2 : U8) (hi : i.val = n % 10)
    (h1 : i1 = UScalar.cast UScalarTy.U8 i) (h2 : i2.val = 48 + i1.val) :
    i2 = UScalar.ofNat (48 + n % 10) (by have := Nat.mod_lt n (by decide : 10 > 0); scalar_tac) := by
  have := Nat.mod_lt n (by decide : 10 > 0)
  rw [UScalar.eq_equiv]
  simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq, h2, h1, UScalar.cast_val_eq, hi]
  simp; omega

@[step]
theorem push_u64_spec (out : alloc.vec.Vec U8) (n : U64)
    (h : out.length + (decimal n.val).length ≤ Usize.max) :
    push_u64 out n ⦃ r => r.val = out.val ++ decimal n.val ⦄ := by
  induction hn : n.val using Nat.strong_induction_on generalizing n out with
  | _ m ih =>
  subst hn
  rw [push_u64]
  have hol : out.length = out.val.length := rfl
  rw [decimal_unfold] at h ⊢
  split
  · rename_i hge
    have hge' : n.val ≥ 10 := by scalar_tac
    simp only [hge', ite_true, List.length_append, List.length_singleton] at h
    step*
    rw [digit_eq n.val i i1 i2 (by assumption) (by assumption) (by assumption)] at *
    clear ih
    simp only [*, List.append_assoc, ite_true, ite_false, List.nil_append]
  · rename_i hge
    have hge' : ¬ n.val ≥ 10 := by scalar_tac
    simp only [hge', ite_false, List.length_append, List.length_singleton, List.length_nil] at h
    step*
    rw [digit_eq n.val i i1 i2 (by assumption) (by assumption) (by assumption)] at *
    clear ih
    simp only [*, List.append_assoc, ite_true, ite_false, List.nil_append]

theorem sub_zero_full (l : List U8) : sub l 0 l.length = l := by
  rw [sub_full]; simp

@[step]
theorem version_to_bytes_spec (v : Version) (h : (printM v.toP).length ≤ Usize.max) :
    version_to_bytes v ⦃ r => r.val = printM v.toP ⦄ := by
  unfold version_to_bytes
  have hn : (alloc.vec.Vec.new U8).val = [] := rfl
  have hpl : v.pre.ident.length = v.pre.ident.val.length := rfl
  have hbl : v.build.ident.length = v.build.ident.val.length := rfl
  simp only [printM, Version.toP, List.length_append, List.length_singleton] at h ⊢
  by_cases hp : v.pre.ident.val.length = 0 <;> by_cases hb : v.build.ident.val.length = 0 <;>
    simp only [hp, hb, ne_eq, not_true_eq_false, not_false_eq_true, ite_true, ite_false,
      List.length_nil, List.length_cons] at h ⊢ <;>
    step*
  iterate 3 (all_goals (try (simp_all [alloc.vec.Vec.length, sub_zero_full]; try omega; done)); all_goals (try step*))

end SemverProofs
