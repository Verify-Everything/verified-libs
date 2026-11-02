import Crc32fast.Spec
import Crc32fast.Bits

/-!
# Algebraic facts about the reference CRC-32

These are the facts the table-driven implementation relies on. All of them are
about the reference spec only; nothing here mentions the Rust code.
-/

namespace Crc32Spec

/-- Feeding a zero byte. -/
def Z (x : BitVec 32) : BitVec 32 := byteStep x 0#8

/-- The register after feeding one byte into a zero register. -/
def B (b : BitVec 8) : BitVec 32 := byteStep 0#32 b

/-- `Z` applied `k` times. -/
def Zn : Nat → BitVec 32 → BitVec 32
  | 0, x => x
  | k + 1, x => Z (Zn k x)

/-- The slice-by-16 table, defined from the spec: entry `k, n` is the register
after feeding byte `n` into a zero register and then `k` zero bytes. -/
def tbl (k : Nat) (n : BitVec 8) : BitVec 32 := Zn k (B n)

/-- The eight bit steps of `byteStep`. -/
def s8 (c : BitVec 32) : BitVec 32 :=
  bitStep (bitStep (bitStep (bitStep (bitStep (bitStep (bitStep (bitStep c)))))))

/-- The bit step is linear over GF(2); everything below follows from this. -/
theorem bitStep_xor (x y : BitVec 32) : bitStep (x ^^^ y) = bitStep x ^^^ bitStep y := by
  simp only [bitStep, BitVec.getLsbD_xor]
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    simp [BitVec.ushiftRight_xor_distrib] <;> ac_nf <;> simp [← BitVec.xor_assoc]

theorem s8_xor (x y : BitVec 32) : s8 (x ^^^ y) = s8 x ^^^ s8 y := by simp only [s8, bitStep_xor]
theorem byteStep_s8 (c : BitVec 32) (b : BitVec 8) : byteStep c b = s8 (c ^^^ b.zeroExtend 32) := rfl
theorem Z_s8 (x : BitVec 32) : Z x = s8 x := by simp [Z, byteStep_s8]
theorem B_s8 (b : BitVec 8) : B b = s8 (b.zeroExtend 32) := by simp [B, byteStep_s8]

/-- One byte step splits into the register part and the data part. -/
theorem byteStep_split (c : BitVec 32) (b : BitVec 8) : byteStep c b = Z c ^^^ B b := by
  rw [byteStep_s8, s8_xor, Z_s8, B_s8]

theorem Z_xor (x y : BitVec 32) : Z (x ^^^ y) = Z x ^^^ Z y := by simp only [Z_s8, s8_xor]

theorem Z_zero : Z 0#32 = 0#32 := by decide

theorem Zn_xor (k : Nat) (x y : BitVec 32) : Zn k (x ^^^ y) = Zn k x ^^^ Zn k y := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Zn, ih, Z_xor]

theorem Zn_add (j k : Nat) (x : BitVec 32) : Zn j (Zn k x) = Zn (j + k) x := by
  induction j with
  | zero => simp [Zn]
  | succ j ih => simp [Zn, ih, Nat.add_right_comm]

theorem zext_xor (a b : BitVec 8) :
    (a ^^^ b).zeroExtend 32 = a.zeroExtend 32 ^^^ b.zeroExtend 32 := by
  bv_bits 32

theorem B_xor (a b : BitVec 8) : B (a ^^^ b) = B a ^^^ B b := by simp only [B_s8, zext_xor, s8_xor]

theorem Z_zext (b : BitVec 8) : Z (b.zeroExtend 32) = B b := by rw [Z_s8, B_s8]

theorem bitStep_shr (x : BitVec 32) (k : Nat) (h : x.getLsbD k = false) :
    bitStep (x >>> k) = x >>> (k + 1) := by
  have h' : (x >>> k).getLsbD 0 = false := by rw [BitVec.getLsbD_ushiftRight]; simpa using h
  simp only [bitStep, h', Bool.false_eq_true, ite_false, shr_shr1]

/-- With the low 8 bits clear, feeding a zero byte is a plain shift. -/
theorem Z_low_zero (x : BitVec 32) (h : x &&& 255#32 = 0#32) : Z x = x >>> 8 := by
  have hb : ∀ i < 8, x.getLsbD i = false := by
    intro i hi
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
    have h255 : (255#32).getLsbD i = true := by
      rcases i with _|_|_|_|_|_|_|_|i <;> first | rfl | omega
    simpa [h255] using this
  have h0 : x = x >>> 0 := by simp
  rw [Z_s8, s8]
  conv => lhs; rw [h0]
  rw [bitStep_shr x 0 (hb 0 (by omega)), bitStep_shr x 1 (hb 1 (by omega)),
    bitStep_shr x 2 (hb 2 (by omega)), bitStep_shr x 3 (hb 3 (by omega)),
    bitStep_shr x 4 (hb 4 (by omega)), bitStep_shr x 5 (hb 5 (by omega)),
    bitStep_shr x 6 (hb 6 (by omega)), bitStep_shr x 7 (hb 7 (by omega))]

theorem tbl_xor (k : Nat) (a b : BitVec 8) : tbl k (a ^^^ b) = tbl k a ^^^ tbl k b := by
  simp [tbl, B_xor, Zn_xor]

/-- The byte-at-a-time table step used by `update_slow`. -/
theorem byteStep_table (c : BitVec 32) (b : BitVec 8) :
    byteStep c b = tbl 0 (c.truncate 8 ^^^ b) ^^^ (c >>> 8) := by
  have hc : c = (c.truncate 8).zeroExtend 32 ^^^ ((c >>> 8) <<< 8) := by bv_bits 32
  rw [byteStep_split, tbl, Zn, B_xor]
  conv => lhs; rw [hc]
  rw [Z_xor, Z_zext, Z_low_zero _ (by bv_bits 32)]
  have : (c >>> 8) <<< 8 >>> 8 = c >>> 8 := by bv_bits 32
  rw [this]; ac_rfl

theorem Z_shl8 (b : BitVec 8) : Z (b.zeroExtend 32 <<< 8) = b.zeroExtend 32 := by
  rw [Z_low_zero _ (by bv_bits 32)]; bv_bits 32

theorem Z_shl16 (b : BitVec 8) : Z (b.zeroExtend 32 <<< 16) = b.zeroExtend 32 <<< 8 := by
  rw [Z_low_zero _ (by bv_bits 32)]; bv_bits 32

theorem Z_shl24 (b : BitVec 8) : Z (b.zeroExtend 32 <<< 24) = b.zeroExtend 32 <<< 16 := by
  rw [Z_low_zero _ (by bv_bits 32)]; bv_bits 32

theorem split_bytes (x : BitVec 32) :
    x = (x.truncate 8).zeroExtend 32 ^^^ ((x >>> 8).truncate 8).zeroExtend 32 <<< 8
      ^^^ ((x >>> 16).truncate 8).zeroExtend 32 <<< 16
      ^^^ ((x >>> 24).truncate 8).zeroExtend 32 <<< 24 := by
  bv_bits 32

/-- Four zero bytes spread a 32-bit register over four table lookups. -/
theorem Z4_bytes (x : BitVec 32) :
    Zn 4 x = tbl 3 (x.truncate 8) ^^^ tbl 2 ((x >>> 8).truncate 8)
      ^^^ tbl 1 ((x >>> 16).truncate 8) ^^^ tbl 0 ((x >>> 24).truncate 8) := by
  conv => lhs; rw [split_bytes x]
  simp only [Zn_xor]
  simp only [Zn, tbl, Z_zext, Z_shl8, Z_shl16, Z_shl24]

/-- Little-endian decode of four bytes. -/
def le32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 := b3 ++ b2 ++ b1 ++ b0

/-- The slice-by-16 step computed by `fold_16`, written with spec-level tables. -/
def fold16 (c : BitVec 32) (b : List (BitVec 8)) : BitVec 32 :=
  let w0 := le32 b[0]! b[1]! b[2]! b[3]! ^^^ c
  tbl 0 b[15]! ^^^ tbl 1 b[14]! ^^^ tbl 2 b[13]! ^^^ tbl 3 b[12]!
  ^^^ tbl 4 b[11]! ^^^ tbl 5 b[10]! ^^^ tbl 6 b[9]! ^^^ tbl 7 b[8]!
  ^^^ tbl 8 b[7]! ^^^ tbl 9 b[6]! ^^^ tbl 10 b[5]! ^^^ tbl 11 b[4]!
  ^^^ tbl 12 ((w0 >>> 24).truncate 8) ^^^ tbl 13 ((w0 >>> 16).truncate 8)
  ^^^ tbl 14 ((w0 >>> 8).truncate 8) ^^^ tbl 15 (w0.truncate 8)

theorem crcRaw16 (c : BitVec 32) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    crcRaw c [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      Zn 16 c ^^^ tbl 15 b0 ^^^ tbl 14 b1 ^^^ tbl 13 b2 ^^^ tbl 12 b3
      ^^^ tbl 11 b4 ^^^ tbl 10 b5 ^^^ tbl 9 b6 ^^^ tbl 8 b7
      ^^^ tbl 7 b8 ^^^ tbl 6 b9 ^^^ tbl 5 b10 ^^^ tbl 4 b11
      ^^^ tbl 3 b12 ^^^ tbl 2 b13 ^^^ tbl 1 b14 ^^^ tbl 0 b15 := by
  simp only [crcRaw, List.foldl, byteStep_split, Z_xor, tbl, Zn]

theorem getLsbD_le32 (b0 b1 b2 b3 : BitVec 8) (i : Nat) :
    (le32 b0 b1 b2 b3).getLsbD i =
      if i < 8 then b0.getLsbD i else if i < 16 then b1.getLsbD (i - 8)
      else if i < 24 then b2.getLsbD (i - 16) else b3.getLsbD (i - 24) := by
  unfold le32
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8]
  · by_cases h16 : i - 8 < 8
    · simp [h8, h16, show i < 16 by omega]
    · by_cases h24 : i - 8 - 8 < 8
      · simp [h8, h16, show ¬ i < 16 by omega, show i < 24 by omega, Nat.sub_sub]
        intro h; exact absurd h (by omega)
      · simp [h8, h16, show ¬ i < 16 by omega, show ¬ i < 24 by omega, Nat.sub_sub]
        intro h; exact absurd h (by omega)

theorem le32_xor_bytes (b0 b1 b2 b3 : BitVec 8) (c : BitVec 32) :
    (le32 b0 b1 b2 b3 ^^^ c).truncate 8 = b0 ^^^ c.truncate 8 ∧
    ((le32 b0 b1 b2 b3 ^^^ c) >>> 8).truncate 8 = b1 ^^^ (c >>> 8).truncate 8 ∧
    ((le32 b0 b1 b2 b3 ^^^ c) >>> 16).truncate 8 = b2 ^^^ (c >>> 16).truncate 8 ∧
    ((le32 b0 b1 b2 b3 ^^^ c) >>> 24).truncate 8 = b3 ^^^ (c >>> 24).truncate 8 := by
  simp only [le32]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits 8

theorem Zn16_bytes (c : BitVec 32) :
    Zn 16 c = tbl 15 (c.truncate 8) ^^^ tbl 14 ((c >>> 8).truncate 8)
      ^^^ tbl 13 ((c >>> 16).truncate 8) ^^^ tbl 12 ((c >>> 24).truncate 8) := by
  rw [← Zn_add 12 4, Z4_bytes]
  simp only [Zn_xor, tbl, Zn_add]

/-- `fold_16`'s table formula equals feeding the 16 bytes one at a time. -/
theorem fold16_eq (c : BitVec 32) (b : List (BitVec 8)) (h : 16 ≤ b.length) :
    fold16 c b = crcRaw c (b.take 16) := by
  match b, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: b10 :: b11 :: b12 :: b13 :: b14 :: b15 :: rest, _ =>
    obtain ⟨h0, h1, h2, h3⟩ := le32_xor_bytes b0 b1 b2 b3 c
    simp only [fold16, List.take, crcRaw16, h0, h1, h2, h3, tbl_xor,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    rw [Zn16_bytes]
    ac_rfl

end Crc32Spec
