import Crc32fast.Hasher
import Crc32fast.CombineSpec

/-!
# `combine::combine` and `Hasher::combine`

`Hasher::combine` merges the checksum of a second block into the first,
given only the second block's checksum and length. We prove it gives the same
result as hashing the concatenation.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif


theorem range_next_i32_lt (s e : I32) (h : s.val < e.val) :
    ∃ s' : I32, s'.val = s.val + 1 ∧
      core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨s, e⟩ = ok (some s, ⟨s', e⟩) := by
  have hb' : s.val + (1#usize).val ≤ IScalar.max IScalarTy.I32 := by scalar_tac
  refine ⟨IScalar.ofIntCore (s.val + (1#usize).val) (by scalar_tac), by simp, ?_⟩
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32, core.iter.range.IScalarStep,
    core.cmp.PartialOrdI32, core.clone.CloneI32, liftFun2, liftFun1, bind_ok,
    core.cmp.impls.PartialOrdI32.lt, core.clone.impls.CloneI32.clone, h, decide_true, ite_true,
    core.iter.range.IScalarStep.forward_checked]
  rw [dif_pos hb', bind_ok]

theorem range_next_i32_ge (s e : I32) (h : ¬ s.val < e.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨s, e⟩ = ok (none, ⟨s, e⟩) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32, core.iter.range.IScalarStep,
    core.cmp.PartialOrdI32, liftFun2, bind_ok, core.cmp.impls.PartialOrdI32.lt, h, decide_false]
  rfl

theorem range_next_u32_lt (s e : U32) (h : s.val < e.val) :
    ∃ s' : U32, s'.val = s.val + 1 ∧
      core.iter.range.IteratorRange.next core.iter.range.StepU32 ⟨s, e⟩ = ok (some s, ⟨s', e⟩) := by
  have hb' : s.val + (1#usize).val ≤ UScalar.max UScalarTy.U32 := by scalar_tac
  refine ⟨UScalar.ofNatCore (s.val + (1#usize).val) (by scalar_tac), by simp, ?_⟩
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepU32, core.iter.range.UScalarStep,
    core.cmp.PartialOrdU32, core.clone.CloneU32, liftFun2, liftFun1, bind_ok,
    core.cmp.impls.PartialOrdU32.lt, core.clone.impls.CloneU32.clone, h, decide_true, ite_true,
    core.iter.range.UScalarStep.forward_checked]
  rw [dif_pos hb', bind_ok]

theorem range_next_u32_ge (s e : U32) (h : ¬ s.val < e.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepU32 ⟨s, e⟩ = ok (none, ⟨s, e⟩) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepU32, core.iter.range.UScalarStep,
    core.cmp.PartialOrdU32, liftFun2, bind_ok, core.cmp.impls.PartialOrdU32.lt, h, decide_false]
  rfl

theorem bitStep_code (b : BitVec 32) : (b >>> 1) ^^^ ((-(b &&& 1#32)) &&& POLY) = bitStep b := by
  rw [and1]; cases h : b.getLsbD 0 <;> simp only [bitStep, h, ite_true, ite_false, Bool.false_eq_true]
  · simp
  · congr 1

theorem mask_code (a b : BitVec 32) (k : Nat) :
    b &&& (-((a >>> k) &&& 1#32)) = if a.getLsbD k then b else 0#32 := by
  have h1 : ∀ x : BitVec 32, x &&& 1#32 = if x.getLsbD 0 then 1#32 else 0#32 := and1
  rw [h1, BitVec.getLsbD_ushiftRight]
  simp only [Nat.add_zero]
  split
  · have : -(1#32) = BitVec.allOnes 32 := by decide
    rw [this, BitVec.and_allOnes]
  · simp

theorem I32.sub_ok (x y : I32) (h1 : IScalar.min .I32 ≤ x.val - y.val) (h2 : x.val - y.val ≤ IScalar.max .I32) :
    ∃ z : I32, z.val = x.val - y.val ∧ (x - y : Result I32) = ok z := by
  simp only [HSub.hSub, IScalar.sub, IScalar.tryMk, IScalar.tryMkOpt]
  have hc : IScalar.check_bounds IScalarTy.I32 (Sub.sub x.val y.val) = true := by
    simp only [IScalar.check_bounds, decide_eq_true_eq]
    show -2 ^ (IScalarTy.I32.numBits - 1) ≤ x.val - y.val ∧ x.val - y.val < 2 ^ (IScalarTy.I32.numBits - 1)
    simp only [IScalar.min, IScalar.max, IScalarTy.numBits] at h1 h2 ⊢
    constructor <;> omega
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

theorem multiply_body_some (a b p : U32) (s e s' : I32)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepI32 ⟨s, e⟩ = ok (some s, ⟨s', e⟩))
    (h0 : 0 ≤ s.val) (h31 : s.val ≤ 31) :
    combine.multiply_loop.body a ⟨s, e⟩ b p =
      ok (.cont (⟨s', e⟩, ⟨bitStep b.bv⟩, ⟨p.bv ^^^ (if a.bv.getLsbD (31 - s.toNat) then b.bv else 0#32)⟩)) := by
  obtain ⟨d, hd, hsub⟩ := I32.sub_ok 31#i32 s (by scalar_tac) (by scalar_tac)
  have hd0 : 0 ≤ d.val := by rw [hd]; simp; omega
  have hdt : d.toNat < 32 := by
    have : d.toNat = (31 - s.val).toNat := by simp [IScalar.toNat, hd]
    omega
  unfold combine.multiply_loop.body
  rw [hnext]
  rw_bind
  rw [uncurry_apply_pair]
  simp only []
  rw [hsub]
  rw_bind
  rw [U32.shr_ok a d hd0 hdt]
  rw_bind
  simp only [lift, core.num.U32.wrapping_neg]
  rw_bind
  rw_bind
  rw_bind
  rw_bind
  rw [U32.shr_ok b 1#i32 (by decide) (by decide)]
  rw_bind
  rw_bind
  rw_bind
  rw_bind
  rw_bind
  have hdn : d.toNat = 31 - s.toNat := by
    have : d.toNat = (31 - s.val).toNat := by simp [hd]
    rw [this]
    show (31 - s.val).toNat = 31 - s.val.toNat
    omega
  have hP : (combine.POLY.bv : BitVec 32) = POLY := by unfold combine.POLY; rfl
  have h1 : (1#i32).toNat = 1 := by decide
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show (_ : U32) = _
    rw [UScalar.eq_equiv_bv_eq, ← bitStep_code]
    unfold combine.POLY
    rfl
  · show (_ : U32) = _
    rw [UScalar.eq_equiv_bv_eq, ← hdn, ← mask_code]
    rfl

theorem multiply_body_none (a b p : U32) (s e : I32) (h : ¬ s.val < e.val) :
    combine.multiply_loop.body a ⟨s, e⟩ b p = ok (.done p) := by
  unfold combine.multiply_loop.body
  rw [range_next_i32_ge s e h]
  rw_bind
  rw [uncurry_apply_pair]

theorem multiply_unfold (it : core.ops.range.Range I32) (a b p : U32) :
    combine.multiply_loop it a b p = (do
      let r ← combine.multiply_loop.body a it b p
      match r with
      | .cont (it', b', p') => combine.multiply_loop it' a b' p'
      | .done x => ok x) := by
  conv => lhs; unfold combine.multiply_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨it', b', p'⟩⟩ | x <;> rfl

theorem multiply_loop_eq (k : Nat) (s : I32) (hs0 : 0 ≤ s.val) (hk : s.val + k = 32) (a b p : U32) :
    combine.multiply_loop ⟨s, 32#i32⟩ a b p = ok ⟨mulLoop a.bv k s.toNat b.bv p.bv⟩ := by
  induction k generalizing s b p with
  | zero =>
    rw [multiply_unfold, multiply_body_none a b p s 32#i32 (by simp; omega), bind_ok]
    rfl
  | succ k ih =>
    obtain ⟨s', hs', hnext⟩ := range_next_i32_lt s 32#i32 (by simp; omega)
    rw [multiply_unfold, multiply_body_some a b p s 32#i32 s' hnext hs0 (by omega), bind_ok]
    simp only []
    rw [ih s' (by omega) (by omega)]
    have : s'.toNat = s.toNat + 1 := by
      show s'.val.toNat = s.val.toNat + 1
      omega
    rw [this]
    rfl

/-- `combine::multiply` computes the spec's carry-less multiply. -/
theorem multiply_eq (a b : U32) : combine.multiply a b = ok ⟨mulSpec a.bv b.bv⟩ := by
  unfold combine.multiply
  rw [multiply_loop_eq 32 0#i32 (by decide) (by decide)]
  rfl

theorem x2n_table_eq : combine.X2N_TABLE.val.map (·.bv) = x2n := by
  unfold combine.X2N_TABLE
  decide +kernel

theorem x2n_index (s : U32) :
    combine.X2N_TABLE.index_usize (UScalar.cast .Usize (s &&& 31#u32)) = ok ⟨x2n[s.val % 32]!⟩ := by
  have hv : (UScalar.cast .Usize (s &&& 31#u32)).val = s.val % 32 := by
    rw [UScalar.cast_val_eq]
    have h1 : (s &&& 31#u32).val = s.val % 32 := by
      show (s.bv &&& 31#32).toNat = s.bv.toNat % 32
      rw [BitVec.toNat_and]
      have := Nat.and_two_pow_sub_one_eq_mod s.bv.toNat 5
      simpa using this
    rw [h1]
    apply Nat.mod_eq_of_lt
    have : s.val % 32 < 32 := Nat.mod_lt _ (by decide)
    have h2 : 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
      cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
    omega
  have hl : (UScalar.cast .Usize (s &&& 31#u32)).val < combine.X2N_TABLE.val.length := by
    rw [hv]; simp; exact Nat.mod_lt _ (by decide)
  rw [Array.index_usize_ok _ _ hl, hv]
  congr 1
  rw [UScalar.eq_equiv_bv_eq]
  have hlt : s.val % 32 < 32 := Nat.mod_lt _ (by decide)
  have := congrArg (fun l => l[s.val % 32]!) x2n_table_eq
  rw [← this]
  have hlen : s.val % 32 < combine.X2N_TABLE.val.length := by simp; omega
  have hm : ∀ (l : List U32) (i : Nat), i < l.length → (l.map (·.bv))[i]! = l[i]!.bv := by
    intro l i h; simp [getElem!_pos, h]
  rw [hm _ _ hlen]

theorem U64.shr_u32_ok (x : U64) (k : U32) (h : k.val < 64) :
    (x >>> k : Result U64) = ok ⟨x.bv >>> k.val⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_UScalar, UScalar.shiftRight]
  rw [if_pos (by simpa using h)]

theorem bit_test (x : U64) (k : Nat) :
    (((⟨x.bv >>> k⟩ : U64) &&& 1#u64) != 0#u64) = decide (x.val / 2 ^ k % 2 = 1) := by
  have h1 : ∀ y : BitVec 64, y &&& 1#64 = if y.getLsbD 0 then 1#64 else 0#64 := and1_64
  have e : (((⟨x.bv >>> k⟩ : U64) &&& 1#u64) != 0#u64) = ((x.bv >>> k &&& 1#64) != 0#64) := by
    rfl
  rw [e, h1, BitVec.getLsbD_ushiftRight, Nat.add_zero, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have hv : x.val = x.bv.toNat := rfl
  rw [hv]
  by_cases hb : x.bv.toNat / 2 ^ k % 2 = 1
  · rw [decide_eq_true hb]; rfl
  · rw [decide_eq_false hb]; rfl

theorem combine_body_some (len2 : U64) (s e s' : U32)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepU32 ⟨s, e⟩ = ok (some s, ⟨s', e⟩))
    (hs : s.val < 64) (p : U32) :
    combine.combine_loop.body len2 ⟨s, e⟩ p =
      ok (.cont (⟨s', e⟩, if len2.val / 2 ^ s.val % 2 = 1 then ⟨Zn (2 ^ s.val) p.bv⟩ else p)) := by
  unfold combine.combine_loop.body
  rw [hnext]
  rw_bind
  rw [uncurry_apply_pair]
  simp only []
  rw [U64.shr_u32_ok len2 s hs]
  rw_bind
  simp only [lift]
  rw_bind
  rw [bit_test]
  by_cases hb : len2.val / 2 ^ s.val % 2 = 1
  · rw [decide_eq_true hb, if_pos rfl, if_pos hb]
    rw_bind
    rw_bind
    rw [x2n_index]
    rw_bind
    rw [multiply_eq]
    rw_bind
    congr 4
    exact mulSpec_x2n s.val p.bv
  · rw [decide_eq_false hb, if_neg (by simp), if_neg hb]

theorem combine_body_none (len2 : U64) (s e : U32) (h : ¬ s.val < e.val) (p : U32) :
    combine.combine_loop.body len2 ⟨s, e⟩ p = ok (.done p) := by
  unfold combine.combine_loop.body
  rw [range_next_u32_ge s e h]
  rw_bind
  rw [uncurry_apply_pair]

theorem combine_unfold (it : core.ops.range.Range U32) (len2 : U64) (p : U32) :
    combine.combine_loop it len2 p = (do
      let r ← combine.combine_loop.body len2 it p
      match r with
      | .cont (it', p') => combine.combine_loop it' len2 p'
      | .done x => ok x) := by
  conv => lhs; unfold combine.combine_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨it', p'⟩⟩ | x <;> rfl

theorem combine_loop_eq (k : Nat) (s n : U32) (hk : s.val + k = n.val) (hn : n.val ≤ 64)
    (len2 : U64) (c1 : BitVec 32) (p : U32) (hp : p.bv = Zn (len2.val % 2 ^ s.val) c1) :
    combine.combine_loop ⟨s, n⟩ len2 p = ok ⟨Zn (len2.val % 2 ^ n.val) c1⟩ := by
  induction k generalizing s p with
  | zero =>
    rw [combine_unfold, combine_body_none len2 s n (by omega) p, bind_ok]
    have : s.val = n.val := by omega
    rw [← this, ← hp]
  | succ k ih =>
    obtain ⟨s', hs', hnext⟩ := range_next_u32_lt s n (by omega)
    rw [combine_unfold, combine_body_some len2 s n s' hnext (by omega) p, bind_ok]
    simp only []
    apply ih s' (by omega)
    rw [hs', Nat.mod_pow_succ]
    split
    · next hb =>
      show Zn (2 ^ s.val) p.bv = _
      rw [hp, Zn_add, hb, Nat.mul_one, Nat.add_comm]
    · next hb =>
      have : len2.val / 2 ^ s.val % 2 = 0 := by omega
      rw [hp, this, Nat.mul_zero, Nat.add_zero]

theorem U32.sub_ok (x y : U32) (h : y.val ≤ x.val) :
    (x - y : Result U32) = ok ⟨BitVec.ofNat _ (x.val - y.val)⟩ := by
  simp only [HSub.hSub, UScalar.sub]
  rw [if_neg (by omega)]

theorem lz_val (x : U64) (hx : x.val ≠ 0) :
    (core.num.U64.leading_zeros x).val = 64 - Nat.log 2 x.val - 1 := by
  have hx' : x.bv ≠ 0#64 := by
    intro h; apply hx; simp [UScalar.val, h]
  have hlog : Nat.log 2 x.val < 64 := by
    have : x.val < 2 ^ 64 := by scalar_tac
    exact Nat.log_lt_of_lt_pow (by omega) this
  show (BitVec.ofNat 32 (BitVec.leadingZeros x.bv)).toNat = _
  simp only [BitVec.leadingZeros, BitVec.toNat_ofNat]
  rw [if_neg (show ¬ x.bv = 0 from hx')]
  have : x.bv.toNat = x.val := rfl
  rw [this]
  apply Nat.mod_eq_of_lt
  omega

/-- `combine::combine` pads `crc1` with `len2` zero bytes and XORs in `crc2`. -/
theorem combine_eq (c1 c2 : U32) (len2 : U64) :
    combine.combine c1 c2 len2 =
      ok (if len2.val = 0 then c1 else ⟨Zn len2.val c1.bv ^^^ c2.bv⟩) := by
  unfold combine.combine
  by_cases h0 : len2 = 0#u64
  · rw [if_pos h0, if_pos (by rw [h0]; rfl)]
  · have hv : len2.val ≠ 0 := by
      intro h; apply h0; rw [UScalar.eq_equiv_bv_eq]; apply BitVec.eq_of_toNat_eq; simpa using h
    rw [if_neg h0, if_neg hv]
    simp only [lift]
    rw_bind
    have hlz := lz_val len2 hv
    have hlog : Nat.log 2 len2.val < 64 := by
      have : len2.val < 2 ^ 64 := by scalar_tac
      exact Nat.log_lt_of_lt_pow (by omega) this
    rw [U32.sub_ok 64#u32 _ (by rw [hlz]; simp; omega)]
    rw_bind
    set n : U32 := ⟨BitVec.ofNat _ ((64#u32).val - (core.num.U64.leading_zeros len2).val)⟩ with hn
    have hnv : n.val = Nat.log 2 len2.val + 1 := by
      rw [hn]
      show (BitVec.ofNat 32 _).toNat = _
      rw [BitVec.toNat_ofNat, hlz]
      simp only [show (64#u32).val = 64 from rfl]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [combine_loop_eq n.val 0#u32 n (by simp) (by omega) len2 c1.bv c1 (by simp [Nat.mod_one]; rfl)]
    rw_bind
    have hlt : len2.val < 2 ^ n.val := by
      rw [hnv]; exact Nat.lt_pow_succ_log_self (by decide) _
    rw [Nat.mod_eq_of_lt hlt]
    rfl

/-- `Hasher::combine`, any input: it never fails, adds the byte counts modulo 2^64, and pads
`self`'s CRC with `other.amount` zero bytes before XORing in `other`'s CRC. -/
theorem hasher_combine_exact (h other : Hasher) :
    h.combine other = ok { h with
      amount := core.num.U64.wrapping_add h.amount other.amount,
      state := if other.amount.val = 0 then h.state else ⟨Zn other.amount.val h.state.bv ^^^ other.state.bv⟩ } := by
  unfold Hasher.combine
  simp only [lift]
  rw_bind
  rw [combine_eq]
  rw_bind

/-- `Hasher::combine`: if `other` holds the CRC-32 of `bs` (and its length), then
combining continues `self`'s checksum with `bs`. -/
theorem hasher_combine_eq (h other : Hasher) (bs : List (BitVec 8))
    (hstate : other.state.bv = crc32 bs) (hamt : other.amount.val = bs.length) :
    h.combine other = ok { h with
      amount := core.num.U64.wrapping_add h.amount other.amount,
      state := ⟨update h.state.bv bs⟩ } := by
  rw [hasher_combine_exact]
  congr 3
  by_cases h0 : other.amount.val = 0
  · rw [if_pos h0]
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [UScalar.eq_equiv_bv_eq, update_nil]
  · rw [if_neg h0, UScalar.eq_equiv_bv_eq, update_eq_Zn_xor, hstate, hamt]

end Crc32fastVerif
