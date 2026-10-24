import Crc32fast.SimdSse

/-!
# `calculate` (PCLMULQDQ, fold by 4) equals the spec's `update`
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec x86

namespace Crc32Spec

/-- The initial CRC goes into the low dword of the first block. -/
theorem zext_basis : ∀ j, j < 32 → R16 ((eW 32 j).setWidth 128) = Zn 16 (eW 32 j) := by
  decide +kernel

theorem R16_zext (c : BitVec 32) : R16 (c.setWidth 128) = Zn 16 c := by
  have hlin : IsLinW (fun c : BitVec 32 => R16 (c.setWidth 128)) := by
    intro a b; simp only [BitVec.setWidth_xor]; exact R16_lin _ _
  have hz : IsLinW (fun c : BitVec 32 => Zn 16 c) := fun a b => Zn_xor 16 a b
  exact linW_ext hlin hz zext_basis c

/-- Four pending blocks, as one CRC register value. -/
def S4 (x3 x2 x1 x0 : BitVec 128) : BitVec 32 :=
  Zn 48 (R16 x3) ^^^ Zn 32 (R16 x2) ^^^ Zn 16 (R16 x1) ^^^ R16 x0

end Crc32Spec

namespace Crc32fastVerif

/-- Consuming one 16-byte block. -/
theorem step16 (c : BitVec 32) (l : List U8) (h : 16 ≤ l.length) :
    crcRaw c (bytes l) = crcRaw (Zn 16 c ^^^ R16 (blk l)) (bytes (l.drop 16)) := by
  have hsplit : bytes l = bytes (l.take 16) ++ bytes (l.drop 16) := by simp [bytes]
  have hlen : (bytes (l.take 16)).length = 16 := by simp [bytes]; omega
  rw [hsplit, crcRaw_append, crcRaw_split c (bytes (l.take 16)), hlen, R16_blk l h]

theorem drop16_val (d : Slice U8) : (d.drop 16#usize).val = d.val.drop 16 := by
  simp [Slice.drop]

theorem len_drop16' (d : Slice U8) : (d.drop 16#usize).length = d.length - 16 := len_drop16 d

/-- One round of the fold-by-4 loop keeps the CRC of everything consumed. -/
theorem step64 (x3 x2 x1 x0 : BitVec 128) (l : List U8) (h : 64 ≤ l.length) :
    crcRaw (S4 x3 x2 x1 x0) (bytes l) =
      crcRaw (S4 (blk l ^^^ F k1k2 x3) (blk (l.drop 16) ^^^ F k1k2 x2)
        (blk (l.drop 32) ^^^ F k1k2 x1) (blk (l.drop 48) ^^^ F k1k2 x0)) (bytes (l.drop 64)) := by
  rw [step16 _ l (by omega), step16 _ (l.drop 16) (by simp; omega), step16 _ ((l.drop 16).drop 16) (by simp; omega),
    step16 _ (((l.drop 16).drop 16).drop 16) (by simp; omega)]
  simp only [List.drop_drop]
  congr 1
  have hx : ∀ a b : BitVec 128, R16 (a ^^^ b) = R16 a ^^^ R16 b := R16_lin
  simp only [S4, hx, ← foldBy64, Zn_xor, Zn_add, Nat.reduceAdd, List.drop_drop]
  ac_rfl

/-- Drop four 16-byte blocks. -/
def drop64 (d : Slice U8) : Slice U8 := (((d.drop 16#usize).drop 16#usize).drop 16#usize).drop 16#usize

theorem drop64_val (d : Slice U8) : (drop64 d).val = d.val.drop 64 := by
  simp only [drop64, drop16_val, List.drop_drop]

theorem drop64_length (d : Slice U8) : (drop64 d).length = d.length - 64 := by
  simp only [Slice.length, drop64_val, List.length_drop]

theorem calc_body_ge (k x3 x2 x1 x0 : BitVec 128) (d : Slice U8) (h : 64 ≤ d.length) :
    specialized.pclmulqdq.calculate_loop.body k d x3 x2 x1 x0 =
      ok (.cont (drop64 d, blk d.val ^^^ F k x3, blk (d.val.drop 16) ^^^ F k x2,
        blk (d.val.drop 32) ^^^ F k x1, blk (d.val.drop 48) ^^^ F k x0)) := by
  unfold specialized.pclmulqdq.calculate_loop.body
  have h1 : 16 ≤ (d.drop 16#usize).length := by rw [len_drop16]; omega
  have h2 : 16 ≤ ((d.drop 16#usize).drop 16#usize).length := by rw [len_drop16, len_drop16]; omega
  have h3 : 16 ≤ (((d.drop 16#usize).drop 16#usize).drop 16#usize).length := by
    rw [len_drop16, len_drop16, len_drop16]; omega
  rw [if_pos (by simp; scalar_tac), get_eq d (by omega)]
  rw_bind; rw [uncurry_apply_pair, reduce128_eq]; rw_bind
  rw [get_eq _ h1]; rw_bind; rw [uncurry_apply_pair, reduce128_eq]; rw_bind
  rw [get_eq _ h2]; rw_bind; rw [uncurry_apply_pair, reduce128_eq]; rw_bind
  rw [get_eq _ h3]; rw_bind; rw [uncurry_apply_pair, reduce128_eq]; rw_bind
  simp only [drop64, drop16_val, List.drop_drop, Nat.reduceAdd]

theorem calc_body_lt (k x3 x2 x1 x0 : BitVec 128) (d : Slice U8) (h : d.length < 64) :
    specialized.pclmulqdq.calculate_loop.body k d x3 x2 x1 x0 = ok (.done (d, x3, x2, x1, x0)) := by
  unfold specialized.pclmulqdq.calculate_loop.body
  rw [if_neg (by simp; scalar_tac)]

theorem calc_unfold (d : Slice U8) (x3 x2 x1 x0 k : BitVec 128) :
    specialized.pclmulqdq.calculate_loop d x3 x2 x1 x0 k = (do
      let r ← specialized.pclmulqdq.calculate_loop.body k d x3 x2 x1 x0
      match r with
      | .cont (d', x3', x2', x1', x0') => specialized.pclmulqdq.calculate_loop d' x3' x2' x1' x0' k
      | .done r => ok r) := by
  conv => lhs; unfold specialized.pclmulqdq.calculate_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨d', x3', x2', x1', x0'⟩⟩ | r <;> rfl

theorem calc_loop_eq (n : Nat) (d : Slice U8) (x3 x2 x1 x0 : BitVec 128) (hn : d.length = n) :
    ∃ d' x3' x2' x1' x0', specialized.pclmulqdq.calculate_loop d x3 x2 x1 x0 k1k2 =
      ok (d', x3', x2', x1', x0') ∧ d'.length < 64 ∧
      crcRaw (S4 x3 x2 x1 x0) (bytes d.val) = crcRaw (S4 x3' x2' x1' x0') (bytes d'.val) := by
  induction n using Nat.strong_induction_on generalizing d x3 x2 x1 x0 with
  | _ n ih =>
    by_cases h : 64 ≤ d.length
    · obtain ⟨d', a, b, c, e, h2, hl2, hc2⟩ := ih (drop64 d).length (by rw [drop64_length]; omega)
        (drop64 d) _ _ _ _ rfl
      refine ⟨d', a, b, c, e, ?_, hl2, ?_⟩
      · rw [calc_unfold, calc_body_ge _ _ _ _ _ _ h, bind_ok]; exact h2
      · rw [← hc2, step64 _ _ _ _ _ h, drop64_val]
    · refine ⟨d, x3, x2, x1, x0, ?_, by omega, rfl⟩
      rw [calc_unfold, calc_body_lt _ _ _ _ _ _ (by omega), bind_ok]

theorem hcast_not (crc : U32) : (UScalar.hcast .I32 (~~~crc)).bv = ~~~crc.bv := by
  simp only [UScalar.hcast]
  exact BitVec.setWidth_eq _

theorem cvt_eq (crc : U32) :
    core.core_arch.x86.sse2._mm_cvtsi32_si128 (UScalar.hcast .I32 (~~~crc)) =
      ok ((~~~crc.bv).setWidth 128) := by
  simp only [core.core_arch.x86.sse2._mm_cvtsi32_si128, hcast_not]

theorem collapse4 (x3 x2 x1 x0 : BitVec 128) :
    R16 (x0 ^^^ F k3k4 (x1 ^^^ F k3k4 (x2 ^^^ F k3k4 x3))) = S4 x3 x2 x1 x0 := by
  have hx : ∀ a b : BitVec 128, R16 (a ^^^ b) = R16 a ^^^ R16 b := R16_lin
  simp only [S4, hx, ← foldBy16, Zn_xor, Zn_add, Nat.reduceAdd]
  ac_rfl

/-- The 128-bit PCLMULQDQ path computes the spec's `update`. -/
theorem calculate_eq (crc : U32) (data : Slice U8) :
    specialized.pclmulqdq.calculate crc data = ok ⟨update crc.bv (bytes data.val)⟩ := by
  have hx : ∀ a b : BitVec 128, R16 (a ^^^ b) = R16 a ^^^ R16 b := R16_lin
  unfold specialized.pclmulqdq.calculate
  by_cases h16 : data.length < 16
  · rw [if_pos (by simp; scalar_tac), update_slow_eq]
  rw [if_neg (by simp; scalar_tac)]
  by_cases h128 : data.length < 128
  · rw [if_pos (by unfold specialized.pclmulqdq.MIN_FOLD_BY_4_BYTES; simp; scalar_tac),
      get_eq data (by omega)]
    rw_bind; rw [uncurry_apply_pair]
    simp only [lift, bind_ok, cvt_eq, core.core_arch.x86.sse2._mm_xor_si128]
    rw [r128_eq]
    congr 2
    simp only [update]
    have hdl : data.val.length = data.length := rfl
    rw [step16 _ data.val (by omega), hx, R16_zext, BitVec.xor_comm (Zn 16 _), drop16_val]
  · rw [if_neg (by unfold specialized.pclmulqdq.MIN_FOLD_BY_4_BYTES; simp; scalar_tac)]
    have h1 : 16 ≤ (data.drop 16#usize).length := by rw [len_drop16]; omega
    have h2 : 16 ≤ ((data.drop 16#usize).drop 16#usize).length := by rw [len_drop16, len_drop16]; omega
    have h3 : 16 ≤ (((data.drop 16#usize).drop 16#usize).drop 16#usize).length := by
      rw [len_drop16, len_drop16, len_drop16]; omega
    rw [get_eq data (by omega)]; rw_bind; rw [uncurry_apply_pair]
    rw [get_eq _ h1]; rw_bind; rw [uncurry_apply_pair]
    rw [get_eq _ h2]; rw_bind; rw [uncurry_apply_pair]
    rw [get_eq _ h3]; rw_bind; rw [uncurry_apply_pair]
    simp only [lift, bind_ok, cvt_eq, core.core_arch.x86.sse2._mm_xor_si128]
    rw [k1k2_eq, bind_ok]
    obtain ⟨d', a, b, c, e, hl, _, hc⟩ := calc_loop_eq _ (drop64 data)
      (blk data.val ^^^ (~~~crc.bv).setWidth 128) (blk (data.drop 16#usize).val)
      (blk ((data.drop 16#usize).drop 16#usize).val)
      (blk (((data.drop 16#usize).drop 16#usize).drop 16#usize).val) rfl
    rw [show (((data.drop 16#usize).drop 16#usize).drop 16#usize).drop 16#usize = drop64 data from rfl, hl,
      bind_ok]
    simp only [uncurry_apply_pair]
    rw [k3k4_eq, bind_ok, reduce128_eq, bind_ok, reduce128_eq, bind_ok,
      reduce128_eq, bind_ok, r128_eq, collapse4, ← hc]
    have hdl : data.val.length = data.length := rfl
    have key : crcRaw
        (S4 (blk data.val ^^^ BitVec.setWidth 128 (~~~crc.bv)) (blk (data.drop 16#usize).val)
          (blk ((data.drop 16#usize).drop 16#usize).val)
          (blk (((data.drop 16#usize).drop 16#usize).drop 16#usize).val))
        (bytes (drop64 data).val) = crcRaw (~~~crc.bv) (bytes data.val) := by
      rw [step16 _ data.val (by omega), step16 _ (data.val.drop 16) (by simp; omega),
        step16 _ ((data.val.drop 16).drop 16) (by simp; omega),
        step16 _ (((data.val.drop 16).drop 16).drop 16) (by simp; omega)]
      simp only [drop64_val, drop16_val, List.drop_drop, Nat.reduceAdd]
      congr 1
      simp only [S4, hx, R16_zext, Zn_xor, Zn_add, Nat.reduceAdd]
      ac_rfl
    rw [key]
    rfl

end Crc32fastVerif
