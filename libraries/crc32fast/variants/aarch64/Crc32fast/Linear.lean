import Crc32fast.CombineSpec

/-!
# GF(2)-linear maps into a CRC register

Two linear maps that agree on the basis vectors agree everywhere. With `decide +kernel` on the
basis this proves identities between bit-level circuits without `bv_decide`.
-/

namespace Crc32Spec

/-! ## Linear maps from `BitVec w` -/

def IsLinW {w : Nat} (f : BitVec w → BitVec 32) : Prop := ∀ x y, f (x ^^^ y) = f x ^^^ f y

theorem IsLinW.map_zero {w} {f : BitVec w → BitVec 32} (hf : IsLinW f) : f 0#w = 0#32 := by
  have h := hf 0#w 0#w
  rw [BitVec.xor_self, BitVec.xor_self] at h
  exact h

/-- Basis vector `j` of width `w`. -/
def eW (w j : Nat) : BitVec w := 1#w <<< j

theorem getLsbD_eW (w j i : Nat) (hi : i < w) : (eW w j).getLsbD i = decide (i = j) := by
  simp only [eW, BitVec.getLsbD_shiftLeft]
  by_cases h : i = j
  · subst h; simp [hi, show 0 < w by omega]
  · by_cases hlt : i < j
    · simp [h, hlt]
    · have : i - j ≠ 0 := by omega
      simp [h, hlt, BitVec.getLsbD_one, this]

/-- The first `n` bits of `x`, one basis vector at a time. -/
def rbW {w : Nat} (x : BitVec w) : Nat → BitVec w
  | 0 => 0#w
  | n + 1 => rbW x n ^^^ (if x.getLsbD n then eW w n else 0#w)

theorem getLsbD_rbW {w} (x : BitVec w) (n i : Nat) (hi : i < w) :
    (rbW x n).getLsbD i = (decide (i < n) && x.getLsbD i) := by
  induction n with
  | zero => simp [rbW]
  | succ n ih =>
    simp only [rbW, BitVec.getLsbD_xor, ih]
    by_cases hx : x.getLsbD n
    · simp only [hx, ite_true, getLsbD_eW w n i hi]
      by_cases h : i = n
      · subst h; simp [hx]
      · by_cases hlt : i < n <;> simp [h, hlt] <;> omega
    · simp only [hx, Bool.false_eq_true, ite_false, BitVec.getLsbD_zero, Bool.bne_false]
      by_cases h : i = n
      · subst h; simp [hx]
      · by_cases hlt : i < n
        · simp [hlt, show i < n + 1 by omega]
        · simp [hlt, show ¬ i < n + 1 by omega]

theorem rbW_eq {w} (x : BitVec w) : rbW x w = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rbW x w i hi]
  simp [hi]

/-- Two linear maps that agree on the basis agree everywhere. -/
theorem linW_ext {w} {f g : BitVec w → BitVec 32} (hf : IsLinW f) (hg : IsLinW g)
    (h : ∀ j, j < w → f (eW w j) = g (eW w j)) : ∀ x, f x = g x := by
  intro x
  have : ∀ n, n ≤ w → f (rbW x n) = g (rbW x n) := by
    intro n
    induction n with
    | zero => intro _; simp [rbW, hf.map_zero, hg.map_zero]
    | succ n ih =>
      intro hn
      simp only [rbW]
      rw [hf, hg, ih (by omega)]
      split
      · rw [h n (by omega)]
      · rw [hf.map_zero, hg.map_zero]
  rw [← rbW_eq x]
  exact this w (Nat.le_refl _)

end Crc32Spec
