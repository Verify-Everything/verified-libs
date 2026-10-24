import Crc32fast.SimdSpec

/-!
# The end of `reduce_128_to_crc`: the partial last block and the Barrett reduction

Both are written here as pure functions that follow the Rust code step by step, so the
code proofs only have to unfold the monadic version.
-/

open x86

namespace Crc32Spec

def mask32 : BitVec 128 := 0#32 ++ 0#32 ++ 0#32 ++ (~~~0#32)
def k5 : BitVec 128 := 0#64 ++ 0x163cd6124#64
def pu : BitVec 128 := 0x1F7011641#64 ++ 0x1DB710641#64

/-- The three folding steps after the last full block, ending in the 32-bit CRC register. -/
def barrett (x : BitVec 128) : BitVec 32 :=
  let x3 := clmulSel 16#32 x k3k4 ^^^ srliBytes 8#32 x
  let x4 := clmulSel 0#32 (x3 &&& mask32) k5 ^^^ srliBytes 4#32 x3
  let t1 := clmulSel 16#32 (x4 &&& mask32) pu
  let t2 := clmulSel 0#32 (t1 &&& mask32) pu
  extract32 1#32 (x4 ^^^ t2)

def seqBytes : BitVec 128 :=
  fromBytes 128 ((List.range 16).map fun i => BitVec.ofNat 8 i)

def set1 (b : BitVec 8) : BitVec 128 := fromBytes 128 (List.replicate 16 b)

/-- Shuffle controls for a tail of `n` bytes (`n - 16` as a byte, then XOR 0x80). -/
def shlCtl (n : Nat) : BitVec 128 := addBytes seqBytes (set1 (BitVec.ofNat 8 (n + 240)))
def shrCtl (n : Nat) : BitVec 128 := shlCtl n ^^^ set1 0x80#8

/-- Merge the last `n < 16` bytes `p` (zero-padded block) into the register `x`. -/
def tailStep (n : Nat) (x p : BitVec 128) : BitVec 128 :=
  (shuffle x (shrCtl n) ^^^ shuffle p (shlCtl n)) ^^^ F k3k4 (shuffle x (shlCtl n))

theorem barrett_basis : ∀ j, j < 128 → barrett (eW 128 j) = R16 (eW 128 j) := by
  decide +kernel

theorem tail_x_basis : ∀ n, n < 16 → 0 < n → ∀ j, j < 128 →
    R16 (tailStep n (eW 128 j) 0#128) = Zn n (R16 (eW 128 j)) := by
  decide +kernel

theorem tail_p_basis : ∀ n, n < 16 → 0 < n → ∀ j, j < 128 →
    R16 (tailStep n 0#128 (eW 128 j)) = Rn (eW 128 j) n := by
  decide +kernel

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
