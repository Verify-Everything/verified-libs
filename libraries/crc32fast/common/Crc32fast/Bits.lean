/-!
# Kernel-checked bit-vector helpers

`bv_decide` would prove these instantly, but it trusts Lean's compiled SAT-certificate checker
(it adds `_native` axioms). Everything here is checked by the kernel instead, so the headline
theorems rest only on Lean's three standard axioms.
-/

namespace Crc32Spec

set_option hygiene false in
/-- Prove a bit-vector identity bit by bit: `ext`, then one `simp` per bit index below `n`. -/
macro "bv_bits" n:num : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  iterate $n (rcases i with _ | i; · simp only [BitVec.getLsbD_append,
    BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_cast, BitVec.getLsbD_not, BitVec.getLsbD_and,
    BitVec.getLsbD_or] <;> simp)
  omega))

theorem and1 (x : BitVec 32) : x &&& 1#32 = if x.getLsbD 0 then 1#32 else 0#32 := by
  ext i hi
  rcases i with _ | i
  · cases hx : x.getLsbD 0 <;> simp only [BitVec.getLsbD_eq_getElem (show 0 < 32 by omega)] at hx <;>
      simp [hx]
  · cases x.getLsbD 0 <;> simp

theorem and1_64 (x : BitVec 64) : x &&& 1#64 = if x.getLsbD 0 then 1#64 else 0#64 := by
  ext i hi
  rcases i with _ | i
  · cases hx : x.getLsbD 0 <;> simp only [BitVec.getLsbD_eq_getElem (show 0 < 64 by omega)] at hx <;>
      simp [hx]
  · cases x.getLsbD 0 <;> simp

theorem shr_shr1 (x : BitVec 32) (k : Nat) : x >>> k >>> 1 = x >>> (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

end Crc32Spec
