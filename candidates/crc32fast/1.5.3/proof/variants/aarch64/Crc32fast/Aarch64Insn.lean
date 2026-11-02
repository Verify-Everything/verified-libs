import Crc32fast.Linear
import Crc32fast.Extracted.Funs

/-!
# The Arm `CRC32B` / `CRC32X` pseudocode equals the spec

`a64.crc32` is the Arm ARM pseudocode. Both it and the spec are GF(2)-linear in
(accumulator, data), so checking the 40 (resp. 96) basis vectors is enough.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

theorem reverse_xor {w : Nat} (x y : BitVec w) : (x ^^^ y).reverse = x.reverse ^^^ y.reverse := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_reverse, BitVec.getLsbD_xor, BitVec.getMsbD_xor]

theorem polyMod_xor {N : Nat} (poly : BitVec 32) (k : Nat) (x y : BitVec N) :
    a64.polyMod poly k (x ^^^ y) = a64.polyMod poly k x ^^^ a64.polyMod poly k y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [a64.polyMod]
    rw [← ih]
    congr 1
    simp only [BitVec.getLsbD_xor]
    generalize BitVec.setWidth N poly <<< k = P
    cases x.getLsbD (32 + k) <;> cases y.getLsbD (32 + k)
    · rfl
    · simp only [Bool.false_bne, Bool.false_eq_true, ite_false, ite_true]; ac_rfl
    · simp only [Bool.bne_false, Bool.false_eq_true, ite_false, ite_true]; ac_rfl
    · simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
      rw [BitVec.xor_comm y P, ← BitVec.xor_assoc, BitVec.xor_assoc x P P, BitVec.xor_self,
        BitVec.xor_zero]

theorem crc32_xor {size : Nat} (a1 a2 : BitVec 32) (v1 v2 : BitVec size) :
    a64.crc32 (a1 ^^^ a2) (v1 ^^^ v2) = a64.crc32 a1 v1 ^^^ a64.crc32 a2 v2 := by
  simp only [a64.crc32]
  rw [← reverse_xor, ← BitVec.setWidth_xor, ← polyMod_xor]
  congr 3
  have hz : ∀ {m k : Nat} (x1 x2 : BitVec m), (x1 ^^^ x2) ++ 0#k = (x1 ++ 0#k) ^^^ (x2 ++ 0#k) := by
    intro m k x1 x2; rw [BitVec.xor_append, BitVec.xor_self]
  rw [reverse_xor, reverse_xor, hz, hz, BitVec.setWidth_xor]
  ac_rfl

/-- `(acc, val)` packed in one vector: `acc` in the low 32 bits. -/
def G8 (z : BitVec 40) : BitVec 32 := a64.crc32 (z.setWidth 32) ((z >>> 32).setWidth 8 : BitVec 8)
def H8 (z : BitVec 40) : BitVec 32 := byteStep (z.setWidth 32) ((z >>> 32).setWidth 8)

theorem crc32b_basis : ∀ j, j < 40 → G8 (eW 40 j) = H8 (eW 40 j) := by decide +kernel

theorem crc32b_spec (acc : BitVec 32) (b : BitVec 8) : a64.crc32 acc b = byteStep acc b := by
  have hG : IsLinW G8 := by
    intro x y; simp only [G8, BitVec.setWidth_xor, BitVec.ushiftRight_xor_distrib, crc32_xor]
  have hH : IsLinW H8 := by
    intro x y
    simp only [H8, byteStep_s8, BitVec.setWidth_xor, BitVec.ushiftRight_xor_distrib, zext_xor,
      BitVec.zeroExtend_eq_setWidth]
    rw [← s8_xor]; congr 1; ac_rfl
  have h := linW_ext hG hH crc32b_basis (b.setWidth 40 <<< 32 ||| acc.setWidth 40)
  have e1 : (b.setWidth 40 <<< 32 ||| acc.setWidth 40).setWidth 32 = acc := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi]
  have e2 : ((b.setWidth 40 <<< 32 ||| acc.setWidth 40) >>> 32).setWidth 8 = b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have : 32 + i < 40 := by omega
    have : i < 40 := by omega
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi, *]
  simp only [G8, H8, e1, e2] at h
  exact h

theorem byteStep_xor2 (c1 c2 : BitVec 32) (b1 b2 : BitVec 8) :
    byteStep (c1 ^^^ c2) (b1 ^^^ b2) = byteStep c1 b1 ^^^ byteStep c2 b2 := by
  simp only [byteStep_s8, zext_xor]
  rw [← s8_xor]; congr 1; ac_rfl

theorem crcRaw_xor2 : ∀ (c1 c2 : BitVec 32) (l1 l2 : List (BitVec 8)), l1.length = l2.length →
    crcRaw (c1 ^^^ c2) (List.zipWith (· ^^^ ·) l1 l2) = crcRaw c1 l1 ^^^ crcRaw c2 l2
  | c1, c2, [], [], _ => rfl
  | c1, c2, b1 :: l1, b2 :: l2, h => by
    simp only [List.zipWith_cons_cons, crcRaw, List.foldl_cons] at *
    rw [byteStep_xor2]
    exact crcRaw_xor2 _ _ l1 l2 (by simpa using h)
  | _, _, [], _ :: _, h => by simp at h
  | _, _, _ :: _, [], h => by simp at h

theorem a64byte_xor (x y : BitVec 64) (k : Nat) : a64.byte (x ^^^ y) k = a64.byte x k ^^^ a64.byte y k := by
  simp only [a64.byte, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

def bytes8 (v : BitVec 64) : List (BitVec 8) := (List.range 8).map (a64.byte v)

theorem bytes8_xor (x y : BitVec 64) : bytes8 (x ^^^ y) = List.zipWith (· ^^^ ·) (bytes8 x) (bytes8 y) := by
  simp only [bytes8, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.zipWith_cons_cons, List.zipWith_nil_left, a64byte_xor]

def G64 (z : BitVec 96) : BitVec 32 := a64.crc32 (z.setWidth 32) ((z >>> 32).setWidth 64 : BitVec 64)
def H64 (z : BitVec 96) : BitVec 32 := crcRaw (z.setWidth 32) (bytes8 ((z >>> 32).setWidth 64))

theorem crc32d_basis : ∀ j, j < 96 → G64 (eW 96 j) = H64 (eW 96 j) := by decide +kernel

theorem crc32d_spec (acc : BitVec 32) (v : BitVec 64) : a64.crc32 acc v = crcRaw acc (bytes8 v) := by
  have hG : IsLinW G64 := by
    intro x y; simp only [G64, BitVec.setWidth_xor, BitVec.ushiftRight_xor_distrib, crc32_xor]
  have hH : IsLinW H64 := by
    intro x y
    simp only [H64, BitVec.setWidth_xor, BitVec.ushiftRight_xor_distrib, bytes8_xor]
    exact crcRaw_xor2 _ _ _ _ (by simp [bytes8])
  have h := linW_ext hG hH crc32d_basis (v.setWidth 96 <<< 32 ||| acc.setWidth 96)
  have e1 : (v.setWidth 96 <<< 32 ||| acc.setWidth 96).setWidth 32 = acc := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi]
  have e2 : ((v.setWidth 96 <<< 32 ||| acc.setWidth 96) >>> 32).setWidth 64 = v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have : 32 + i < 96 := by omega
    have : i < 96 := by omega
    simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hi, *]
  simp only [G64, H64, e1, e2] at h
  exact h

end Crc32fastVerif
