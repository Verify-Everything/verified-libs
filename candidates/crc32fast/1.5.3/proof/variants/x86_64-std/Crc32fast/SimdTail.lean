import Crc32fast.SimdTailBarrett
import Crc32fast.SimdTailX1
import Crc32fast.SimdTailX2
import Crc32fast.SimdTailX3
import Crc32fast.SimdTailX4
import Crc32fast.SimdTailP1
import Crc32fast.SimdTailP2
import Crc32fast.SimdTailP3
import Crc32fast.SimdTailP4

/-!
# The end of `reduce_128_to_crc`: the partial last block and the Barrett reduction

Definitions are in `SimdTailDefs`; the kernel-checked basis cases are in `SimdTailBarrett`,
`SimdTailX1..X4` and `SimdTailP1..P4` (split by tail length to keep each module's memory low).
-/

open x86

namespace Crc32Spec

theorem tail_x_basis : ∀ n, n < 16 → 0 < n → ∀ j, j < 128 →
    R16 (tailStep n (eW 128 j) 0#128) = Zn n (R16 (eW 128 j)) := by
  intro n h1 h0
  if h4 : n < 4 then exact tail_x_basis1 n h4 (by omega)
  else if h8 : n < 8 then exact tail_x_basis2 n h8 (by omega)
  else if h12 : n < 12 then exact tail_x_basis3 n h12 (by omega)
  else exact tail_x_basis4 n h1 (by omega)

theorem tail_p_basis : ∀ n, n < 16 → 0 < n → ∀ j, j < 128 →
    R16 (tailStep n 0#128 (eW 128 j)) = Rn (eW 128 j) n := by
  intro n h1 h0
  if h4 : n < 4 then exact tail_p_basis1 n h4 (by omega)
  else if h8 : n < 8 then exact tail_p_basis2 n h8 (by omega)
  else if h12 : n < 12 then exact tail_p_basis3 n h12 (by omega)
  else exact tail_p_basis4 n h1 (by omega)

/-! ## Linearity, then the general statements -/

theorem clmulSel_xor (imm : BitVec 32) (a b c : BitVec 128) :
    clmulSel imm (a ^^^ b) c = clmulSel imm a c ^^^ clmulSel imm b c := by
  unfold clmulSel
  split <;> simp only [lo64_xor, hi64_xor, clmul_xor]

theorem srliBytes_xor (imm : BitVec 32) (a b : BitVec 128) :
    srliBytes imm (a ^^^ b) = srliBytes imm a ^^^ srliBytes imm b := by
  unfold srliBytes
  split
  · simp
  · simp [BitVec.ushiftRight_xor_distrib]

theorem and_xor_left (a b m : BitVec 128) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> rfl

theorem extract32_xor (imm : BitVec 32) (a b : BitVec 128) :
    extract32 imm (a ^^^ b) = extract32 imm a ^^^ extract32 imm b := by
  simp [extract32, BitVec.ushiftRight_xor_distrib]

theorem barrett_lin : IsLinW barrett := by
  intro x y
  simp only [barrett, clmulSel_xor, srliBytes_xor, and_xor_left, extract32_xor]
  ac_rfl

/-- The Barrett reduction returns the CRC register of the block. -/
theorem barrett_eq (x : BitVec 128) : barrett x = R16 x :=
  linW_ext barrett_lin R16_lin barrett_basis x

theorem tailStep_xor (n : Nat) (x y p q : BitVec 128) :
    tailStep n (x ^^^ y) (p ^^^ q) = tailStep n x p ^^^ tailStep n y q := by
  simp only [tailStep, shuffle_xor, F_xor]
  ac_rfl

/-- Merging an `n`-byte tail: the result's CRC register equals feeding the block, then the
    first `n` bytes of `p`. -/
theorem tailStep_eq (n : Nat) (hn : n < 16) (h0 : 0 < n) (x p : BitVec 128) :
    R16 (tailStep n x p) = Zn n (R16 x) ^^^ Rn p n := by
  have hsplit : tailStep n x p = tailStep n x 0#128 ^^^ tailStep n 0#128 p := by
    rw [← tailStep_xor]; simp
  have hx : R16 (tailStep n x 0#128) = Zn n (R16 x) := by
    refine linW_ext (f := fun x => R16 (tailStep n x 0#128)) ?_ (Zn_comp_lin n R16_lin)
      (tail_x_basis n hn h0) x
    intro a b
    simp only []
    rw [show (0#128 : BitVec 128) = 0#128 ^^^ 0#128 by simp, tailStep_xor, R16_lin]
    simp
  have hp : R16 (tailStep n 0#128 p) = Rn p n := by
    refine linW_ext (f := fun p => R16 (tailStep n 0#128 p)) (g := fun p => Rn p n) ?_
      (fun a b => Rn_xor a b n) (tail_p_basis n hn h0) p
    intro a b
    simp only []
    rw [show (0#128 : BitVec 128) = 0#128 ^^^ 0#128 by simp, tailStep_xor, R16_lin]
    simp
  rw [hsplit, R16_lin, hx, hp]

end Crc32Spec
