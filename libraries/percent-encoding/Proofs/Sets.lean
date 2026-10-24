/-
  Properties of `AsciiSet::add` and the two built-in sets.

  This is a plain (non-`module`) file on purpose: `UScalar.wrapping_shl` in the
  Aeneas library is not `@[expose]`d, so its body (needed to evaluate the
  `CONTROLS` constant) is only visible from non-module files.
-/
import Proofs.Code

open Aeneas Aeneas.Std Result WP
open percent_encoding percent_encoding.Spec

namespace percent_encoding.Proofs

theorem testBit_or_two_pow (x k j : Nat) :
    (x ||| 2 ^ k).testBit j = (x.testBit j || decide (k = j)) := by
  simp [Nat.testBit_or, Nat.testBit_two_pow]

/-- `add` inserts exactly one byte (ASCII bytes only; see the panic note in the report). -/
@[step]
theorem add_spec (s : ascii_set.AsciiSet) (b : Std.U8) (hb : b.val < 128) :
    ascii_set.AsciiSet.add s b ⦃ s' => ∀ c, inSet s' c = (decide (c = b.val ∧ c < 128) || inSet s c) ⦄ := by
  unfold ascii_set.AsciiSet.add
  step*
  have hi : i.val = b.val := by simp [i_post]
  have hi4 : i4.val = b.val := by simp [i4_post]
  have hi5 : i5.val = b.val / 32 := by rw [i5_post, hi4, i1_post]
  have hi3 : i3.val = 2 ^ (b.val % 32) := by
    rw [i3_post, i2_post, hi, i1_post, Nat.one_shiftLeft]
    apply Nat.mod_eq_of_lt
    have h32 : b.val % 32 < 32 := by omega
    calc 2 ^ (b.val % 32) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) h32
      _ = U32.size := by simp [U32.size, U32.numBits, UScalarTy.numBits]
  have hi7 : i7.val = i6.val ||| 2 ^ (b.val % 32) := by rw [i7_post, ← hi3]; simp
  have hlen : (s.mask.val).length = 4 := by simp
  have hi6 : i6 = s.mask.val[b.val / 32]! := by
    rw [getElem!_pos s.mask.val (b.val / 32) (by rw [hlen]; omega)]
    simp only [i6_post, hi5]
  intro c
  simp only [inSet, mask_post]
  by_cases hc : c < 128
  · simp only [hc, decide_true, Bool.true_and, and_true]
    have hcl : c / 32 < 4 := by omega
    have hbl : b.val / 32 < 4 := by omega
    by_cases hq : c / 32 = b.val / 32
    · have hset : (s.mask.set i5 i7).val[c / 32]! = i7 := by
        simp only [Array.set_val_eq, hi5, hq]
        rw [getElem!_pos _ _ (by simp; omega)]
        simp
      rw [hset, hi7, testBit_or_two_pow, hi6, ← hq]
      by_cases hcb : c = b.val
      · subst hcb; simp
      · have : b.val % 32 ≠ c % 32 := by omega
        simp [hcb, this, Bool.or_comm]
    · have hset : (s.mask.set i5 i7).val[c / 32]! = s.mask.val[c / 32]! := by
        simp only [Array.set_val_eq, hi5]
        rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
        simp [List.getElem_set, Ne.symm hq]
      have hcb : c ≠ b.val := by rintro rfl; exact hq rfl
      rw [hset]; simp [hcb]
  · simp [hc]

theorem inSet_eq_map (s : ascii_set.AsciiSet) (c : Nat) :
    inSet s c = (decide (c < 128) && ((s.mask.val.map (·.val))[c / 32]!).testBit (c % 32)) := by
  unfold inSet
  by_cases hc : c < 128
  · have hl : c / 32 < (s.mask.val).length := by simp; omega
    rw [getElem!_pos s.mask.val (c / 32) hl,
      getElem!_pos (s.mask.val.map (·.val)) (c / 32) (by simpa using hl)]
    simp
  · simp [hc]

/-- `CONTROLS` is exactly C0 controls (0x00..0x1F) and DEL (0x7F). -/
theorem CONTROLS_spec :
    ascii_set.CONTROLS ⦃ s => ∀ c, inSet s c = decide (c < 32 ∨ c = 127) ⦄ := by
  unfold ascii_set.CONTROLS
  step*
  have h2 : i2 = 31#u32 := by rw [UScalar.eq_equiv]; simp [i2_post]
  subst h2 i1_post i3_post
  have hm : ((Array.make 4#usize [~~~0#u32, 0#u32, 0#u32, U32.wrapping_shl 1#u32 31#u32]
      (by simp)).val.map (·.val)) = [4294967295, 0, 0, 2147483648] := by decide +kernel
  intro c
  rw [inSet_eq_map]
  simp only [hm]
  by_cases hc : c < 128
  · revert c; decide
  · simp [hc]; omega

def isAlnum (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)

/-- `NON_ALPHANUMERIC` is every ASCII byte except `0-9A-Za-z`. -/
theorem NON_ALPHANUMERIC_spec :
    ascii_set.NON_ALPHANUMERIC ⦃ s => ∀ c, inSet s c = decide (c < 128 ∧ isAlnum c = false) ⦄ := by
  unfold ascii_set.NON_ALPHANUMERIC
  step with CONTROLS_spec
  step*
  simp only [*]
  by_cases hc : c < 128
  · revert c; decide +kernel
  · simp [hc]; omega

/-- Every non-alphanumeric byte (including all non-ASCII bytes) gets encoded,
    and `%` in particular, so the round-trip theorem applies. -/
theorem NON_ALPHANUMERIC_should :
    ascii_set.NON_ALPHANUMERIC ⦃ s => ∀ c < 256, shouldEncode s c = !isAlnum c ⦄ := by
  apply WP.spec_mono NON_ALPHANUMERIC_spec
  intro s hs c hc
  simp only [shouldEncode, hs]
  revert c; decide +kernel

/-- The Rust round trip, specialised to `NON_ALPHANUMERIC`: no side condition. -/
theorem roundtrip_NON_ALPHANUMERIC (input encoded : Slice Std.U8) :
    ascii_set.NON_ALPHANUMERIC ⦃ s =>
      bytes encoded = encode s (bytes input) →
      (do let d ← percent_decode encoded
          decodeCollect (encoded.length + 1) d) ⦃ out => out = bytes input ⦄ ⦄ := by
  apply WP.spec_mono NON_ALPHANUMERIC_should
  intro s hs henc
  exact percent_roundtrip input s (by rw [hs 37 (by omega)]; decide) encoded henc

/-- With `CONTROLS`, `%` is not encoded, so the round trip fails: the input
    `%41` encodes to itself and then decodes to `A`. -/
theorem CONTROLS_no_roundtrip :
    ascii_set.CONTROLS ⦃ s => decode (encode s [37, 52, 49]) = [65] ⦄ := by
  apply WP.spec_mono CONTROLS_spec
  intro s hs
  have : ∀ c < 256, shouldEncode s c = decide (128 ≤ c ∨ c < 32 ∨ c = 127) := by
    intro c hc; simp only [shouldEncode, hs]; revert c; decide +kernel
  have h37 := this 37 (by omega)
  have h52 := this 52 (by omega)
  have h49 := this 49 (by omega)
  simp only [encode, h37, h52, h49]
  simp only [decide_eq_true_eq]
  norm_num
  rw [decode_pct]
  simp [afterPct, hexVal, decode]

theorem inSet_eq_chunk (s : ascii_set.AsciiSet) (c : Nat) :
    inSet s c = (decide (c < 128) && (s.mask.val[c / 32]!).val.testBit (c % 32)) := rfl

theorem u32_not_testBit (x : Std.U32) (j : Nat) (hj : j < 32) :
    (~~~x).val.testBit j = !x.val.testBit j := by
  rw [← UScalar.bv_toNat, ← UScalar.bv_toNat, ← BitVec.getLsbD, ← BitVec.getLsbD]
  change (~~~x.bv).getLsbD j = _
  rw [BitVec.getLsbD_not]
  simp [hj]

theorem u32_not_testBit' (x : Std.U32) (j : Nat) (hj : j < 32) :
    (({ bv := ~~~x.bv } : Std.U32)).val.testBit j = !x.val.testBit j :=
  u32_not_testBit x j hj

theorem mask_getElem! (s : ascii_set.AsciiSet) (k : Nat) (hk : k < 4) :
    s.mask.val[k]! = s.mask.val[k]'(by simp; omega) :=
  getElem!_pos s.mask.val k (by simp; omega)

theorem chunk_cases (c : Nat) (hc : c < 128) :
    c / 32 = 0 ∨ c / 32 = 1 ∨ c / 32 = 2 ∨ c / 32 = 3 := by omega

/-- `remove` deletes exactly one ASCII byte. -/
@[step]
theorem remove_spec (s : ascii_set.AsciiSet) (b : Std.U8) (hb : b.val < 128) :
    ascii_set.AsciiSet.remove s b ⦃ s' => ∀ c, inSet s' c = (decide (c ≠ b.val) && inSet s c) ⦄ := by
  unfold ascii_set.AsciiSet.remove
  step*
  have hi : i.val = b.val := by simp [i_post]
  have hi5 : i5.val = b.val := by simp [i5_post]
  have hi6 : i6.val = b.val / 32 := by rw [i6_post, hi5, i1_post]
  have hi3 : i3.val = 2 ^ (b.val % 32) := by
    rw [i3_post, i2_post, hi, i1_post, Nat.one_shiftLeft]
    apply Nat.mod_eq_of_lt
    have h32 : b.val % 32 < 32 := by omega
    calc 2 ^ (b.val % 32) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) h32
      _ = U32.size := by simp [U32.size, U32.numBits, UScalarTy.numBits]
  have hlen : (s.mask.val).length = 4 := by simp
  have hi7 : i7 = s.mask.val[b.val / 32]! := by
    rw [getElem!_pos s.mask.val (b.val / 32) (by rw [hlen]; omega)]
    simp only [i7_post, hi6]
  have hbit : ∀ j < 32, i8.val.testBit j = (i7.val.testBit j && !decide (b.val % 32 = j)) := by
    intro j hj
    rw [i8_post, UScalar.val_and, Nat.testBit_and, i4_post, u32_not_testBit _ _ hj, hi3,
      Nat.testBit_two_pow]
  intro c
  simp only [inSet, mask_post]
  by_cases hc : c < 128
  · simp only [hc, decide_true, Bool.true_and, Bool.and_true]
    have hcl : c / 32 < 4 := by omega
    by_cases hq : c / 32 = b.val / 32
    · have hset : (s.mask.set i6 i8).val[c / 32]! = i8 := by
        simp only [Array.set_val_eq, hi6, hq]
        rw [getElem!_pos _ _ (by simp; omega)]
        simp
      rw [hset, hbit _ (by omega), hi7, ← hq]
      by_cases hcb : c = b.val
      · subst hcb; simp
      · have : b.val % 32 ≠ c % 32 := by omega
        simp [hcb, this]
    · have hset : (s.mask.set i6 i8).val[c / 32]! = s.mask.val[c / 32]! := by
        simp only [Array.set_val_eq, hi6]
        rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]
        simp [List.getElem_set, Ne.symm hq]
      have hcb : c ≠ b.val := by rintro rfl; exact hq rfl
      rw [hset]; simp [hcb]
  · simp [hc]

/-- `union` (and `+`) is set union. -/
@[step]
theorem union_spec (s o : ascii_set.AsciiSet) :
    ascii_set.AsciiSet.union s o ⦃ u => ∀ c, inSet u c = (inSet s c || inSet o c) ⦄ := by
  unfold ascii_set.AsciiSet.union
  step*
  intro c
  simp only [inSet_eq_chunk]
  by_cases hc : c < 128
  · rcases chunk_cases c hc with h | h | h | h <;>
      simp [h, hc, mask_getElem!, Nat.testBit_or, *]
  · simp [hc]

theorem add_op_spec (s o : ascii_set.AsciiSet) :
    ascii_set.AsciiSet.Insts.CoreOpsArithAddAsciiSetAsciiSet.add s o
      ⦃ u => ∀ c, inSet u c = (inSet s c || inSet o c) ⦄ := by
  unfold ascii_set.AsciiSet.Insts.CoreOpsArithAddAsciiSetAsciiSet.add
  exact union_spec s o

/-- `complement` (and `!`) flips every ASCII byte; non-ASCII bytes stay out of the set
    (they are always percent-encoded anyway). -/
@[step]
theorem complement_spec (s : ascii_set.AsciiSet) :
    ascii_set.AsciiSet.complement s ⦃ u => ∀ c, inSet u c = (decide (c < 128) && !inSet s c) ⦄ := by
  unfold ascii_set.AsciiSet.complement
  step*
  intro c
  simp only [inSet_eq_chunk]
  by_cases hc : c < 128
  · have hb : c % 32 < 32 := by omega
    rcases chunk_cases c hc with h | h | h | h <;>
      simp [h, hc, mask_getElem!, u32_not_testBit' _ _ hb, *]
  · simp [hc]

theorem not_op_spec (s : ascii_set.AsciiSet) :
    ascii_set.AsciiSet.Insts.CoreOpsBitNotAsciiSet.not s
      ⦃ u => ∀ c, inSet u c = (decide (c < 128) && !inSet s c) ⦄ := by
  unfold ascii_set.AsciiSet.Insts.CoreOpsBitNotAsciiSet.not
  exact complement_spec s

end percent_encoding.Proofs
