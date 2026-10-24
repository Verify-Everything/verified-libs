import Crc32fast.CombineSpec
import Crc32fast.Extracted.Funs

/-!
# Math behind the x86 SIMD path

A 128-bit register holds 16 bytes of pending data. `R16 x` is the CRC register you get by
feeding those 16 bytes into a zero register. Every SIMD step is GF(2)-linear in the
registers, so each identity below is checked on basis vectors with `decide +kernel`
after proving both sides linear.
-/

open x86

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

/-! ## Bytes of a register -/

/-- The first `n` bytes of a register, in memory order. -/
def bytesOf {w : Nat} (x : BitVec w) (n : Nat) : List (BitVec 8) := (List.range n).map (byte x)

/-- Feed the first `n` bytes of `x` into a zero register. -/
def Rn {w : Nat} (x : BitVec w) (n : Nat) : BitVec 32 := crcRaw 0#32 (bytesOf x n)

/-- The CRC register value of a 128-bit block. -/
def R16 (x : BitVec 128) : BitVec 32 := Rn x 16

/-- The 128-bit fold step `reduce128`: `F k a` is what gets XORed into the next block. -/
def F (k a : BitVec 128) : BitVec 128 := clmul (lo64 a) (lo64 k) ^^^ clmul (hi64 a) (hi64 k)

def k1k2 : BitVec 128 := (0x1c6e41596#64) ++ (0x154442bd4#64)
def k3k4 : BitVec 128 := (0x0ccaa009e#64) ++ (0x1751997d0#64)

theorem fold64_basis : ∀ j, j < 128 → Zn 64 (R16 (eW 128 j)) = R16 (F k1k2 (eW 128 j)) := by
  decide +kernel

theorem fold16_basis : ∀ j, j < 128 → Zn 16 (R16 (eW 128 j)) = R16 (F k3k4 (eW 128 j)) := by
  decide +kernel

/-! ## Linearity of the pieces -/

theorem getLsbD_byte {w} (x : BitVec w) (k i : Nat) :
    (byte x k).getLsbD i = (decide (i < 8) && x.getLsbD (8 * k + i)) := by
  simp [byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Nat.add_comm]

theorem byte_xor {w} (x y : BitVec w) (k : Nat) : byte (x ^^^ y) k = byte x k ^^^ byte y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_byte, BitVec.getLsbD_xor]
  simp [hi]

theorem bytesOf_succ {w} (x : BitVec w) (n : Nat) : bytesOf x (n + 1) = bytesOf x n ++ [byte x n] := by
  simp [bytesOf, List.range_succ]

theorem Rn_zero {w} (x : BitVec w) : Rn x 0 = 0#32 := rfl

theorem Rn_succ {w} (x : BitVec w) (n : Nat) : Rn x (n + 1) = byteStep (Rn x n) (byte x n) := by
  simp only [Rn, bytesOf_succ, crcRaw_append]; rfl

theorem Rn_xor {w} (x y : BitVec w) (n : Nat) : Rn (x ^^^ y) n = Rn x n ^^^ Rn y n := by
  induction n with
  | zero => simp [Rn_zero]
  | succ n ih =>
    rw [Rn_succ, Rn_succ, Rn_succ, ih, byte_xor, byteStep_split, byteStep_split, byteStep_split,
      Z_xor, B_xor]
    ac_rfl

theorem R16_lin : IsLinW R16 := fun x y => Rn_xor x y 16

theorem Zn_comp_lin {w} {f : BitVec w → BitVec 32} (n : Nat) (hf : IsLinW f) :
    IsLinW (fun x => Zn n (f x)) := by
  intro x y; simp only []; rw [hf, Zn_xor]

theorem clmulN_xor (a b c : BitVec 64) (n : Nat) : clmulN (a ^^^ b) c n = clmulN a c n ^^^ clmulN b c n := by
  induction n with
  | zero => simp [clmulN]
  | succ n ih =>
    simp only [clmulN, ih, BitVec.getLsbD_xor]
    cases a.getLsbD n <;> cases b.getLsbD n <;> simp <;> ac_nf <;> simp [← BitVec.xor_assoc]

theorem clmul_xor (a b c : BitVec 64) : clmul (a ^^^ b) c = clmul a c ^^^ clmul b c := clmulN_xor a b c 64

theorem lo64_xor (x y : BitVec 128) : lo64 (x ^^^ y) = lo64 x ^^^ lo64 y := by
  simp [lo64]
theorem hi64_xor (x y : BitVec 128) : hi64 (x ^^^ y) = hi64 x ^^^ hi64 y := by
  simp [hi64, BitVec.ushiftRight_xor_distrib]

theorem F_xor (k x y : BitVec 128) : F k (x ^^^ y) = F k x ^^^ F k y := by
  simp only [F, lo64_xor, hi64_xor, clmul_xor]; ac_rfl

theorem comp_lin {w} {f : BitVec 128 → BitVec 32} {g : BitVec w → BitVec 128} (hf : IsLinW f)
    (hg : ∀ x y, g (x ^^^ y) = g x ^^^ g y) : IsLinW (fun x => f (g x)) := by
  intro x y; simp only []; rw [hg, hf]

/-- Folding a block forward by 64 bytes. -/
theorem foldBy64 (a : BitVec 128) : Zn 64 (R16 a) = R16 (F k1k2 a) :=
  linW_ext (Zn_comp_lin 64 R16_lin) (comp_lin R16_lin (F_xor k1k2)) fold64_basis a

/-- Folding a block forward by 16 bytes. -/
theorem foldBy16 (a : BitVec 128) : Zn 16 (R16 a) = R16 (F k3k4 a) :=
  linW_ext (Zn_comp_lin 16 R16_lin) (comp_lin R16_lin (F_xor k3k4)) fold16_basis a

/-! ## Registers built from bytes -/

theorem fromBytes_cons (w : Nat) (b : BitVec 8) (l : List (BitVec 8)) :
    fromBytes w (b :: l) = b.setWidth w ^^^ (fromBytes w l <<< 8) := rfl

theorem byte_fromBytes_zero (w : Nat) (b : BitVec 8) (l : List (BitVec 8)) (hw : 8 ≤ w) :
    byte (fromBytes w (b :: l)) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_byte, fromBytes_cons]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  simp [hi, show i < w by omega]

theorem byte_fromBytes_succ (w : Nat) (b : BitVec 8) (l : List (BitVec 8)) (k : Nat)
    (hw : 8 * (k + 2) ≤ w) : byte (fromBytes w (b :: l)) (k + 1) = byte (fromBytes w l) k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_byte, getLsbD_byte, fromBytes_cons]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
  have h1 : b.getLsbD (8 * (k + 1) + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
  have h2 : 8 * (k + 1) + i - 8 = 8 * k + i := by omega
  simp [hi, h1, h2, show 8 * (k + 1) + i < w by omega, show ¬ 8 * (k + 1) + i < 8 by omega]

theorem byte_fromBytes (w : Nat) (l : List (BitVec 8)) (k : Nat) (hk : k < l.length)
    (hw : 8 * (k + 1) ≤ w) : byte (fromBytes w l) k = l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons b l ih =>
    rcases k with _ | k
    · simpa using byte_fromBytes_zero w b l (by omega)
    · rw [byte_fromBytes_succ w b l k (by omega)]
      simpa using ih k (by simp at hk; omega) (by omega)

theorem bytesOf_fromBytes (w : Nat) (l : List (BitVec 8)) (hw : 8 * l.length ≤ w) :
    bytesOf (fromBytes w l) l.length = l := by
  apply List.ext_getElem
  · simp [bytesOf]
  · intro k h1 h2
    simp only [bytesOf, List.getElem_map, List.getElem_range]
    exact byte_fromBytes w l k h2 (by omega)

theorem fromBytes_map_xor (w : Nat) (l : List Nat) (f g : Nat → BitVec 8) :
    fromBytes w (l.map fun i => f i ^^^ g i) = fromBytes w (l.map f) ^^^ fromBytes w (l.map g) := by
  induction l with
  | nil => simp [fromBytes]
  | cons i l ih =>
    simp only [List.map_cons, fromBytes_cons, ih, BitVec.shiftLeft_xor_distrib, BitVec.setWidth_xor]
    ac_rfl

theorem shuffle_xor (a b c : BitVec 128) : shuffle (a ^^^ b) c = shuffle a c ^^^ shuffle b c := by
  simp only [shuffle]
  rw [← fromBytes_map_xor]
  congr 1
  apply List.map_congr_left
  intro i _
  split <;> simp [byte_xor]

end Crc32Spec
