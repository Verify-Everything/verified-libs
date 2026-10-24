import Crc32fast.SimdCalc

/-!
# Registers wider than 128 bits, as lists of 128-bit lanes
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec x86

namespace Crc32fastVerif

theorem getLsbD_fromBytes (w : Nat) (l : List (BitVec 8)) (i : Nat) :
    (fromBytes w l).getLsbD i = (decide (i < w) && ((l[i / 8]?).getD 0#8).getLsbD (i % 8)) := by
  induction l generalizing i with
  | nil => simp [fromBytes]
  | cons b l ih =>
    simp only [fromBytes, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
    by_cases h8 : i < 8
    · have h0 : i / 8 = 0 := by omega
      have hm : i % 8 = i := by omega
      simp [h0, hm, h8]
    · have hb : b.getLsbD i = false := BitVec.getLsbD_of_ge b i (by omega)
      have hd : i / 8 = (i - 8) / 8 + 1 := by omega
      have hm : i % 8 = (i - 8) % 8 := by omega
      rw [ih, hb, hd, hm]
      by_cases hw : i < w
      · have : i - 8 < w := by omega
        simp [hw, h8, this]
      · simp [hw]

/-- A 32-byte load is two 16-byte blocks, the first in the low lane. -/
theorem fromBytes256 (l : List U8) :
    fromBytes 256 (bytes (l.take 32)) = blk (l.drop 16) ++ blk l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [blk, BitVec.getLsbD_append, getLsbD_fromBytes, bytes, List.map_take, List.getElem?_take,
    List.map_drop, List.getElem?_drop]
  by_cases h1 : i < 128
  · have : i / 8 < 16 := by omega
    have : i / 8 < 32 := by omega
    simp [*]
  · have e1 : (i - 128) / 8 = i / 8 - 16 := by omega
    have e2 : (i - 128) % 8 = i % 8 := by omega
    have e3 : 16 + (i / 8 - 16) = i / 8 := by omega
    have : i / 8 < 32 := by omega
    have : i / 8 - 16 < 16 := by omega
    have : i - 128 < 128 := by omega
    simp [*]

/-- A 64-byte load is four 16-byte blocks, in increasing lanes. -/
theorem fromBytes512 (l : List U8) :
    fromBytes 512 (bytes (l.take 64)) =
      blk (l.drop 48) ++ blk (l.drop 32) ++ blk (l.drop 16) ++ blk l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [blk, BitVec.getLsbD_append, getLsbD_fromBytes, bytes, List.map_take, List.getElem?_take,
    List.map_drop, List.getElem?_drop]
  have : i / 8 < 64 := by omega
  by_cases h1 : i < 128
  · have : i / 8 < 16 := by omega
    simp [*]
  by_cases h2 : i < 256
  · have e1 : (i - 128) / 8 = i / 8 - 16 := by omega
    have e2 : (i - 128) % 8 = i % 8 := by omega
    have e3 : 16 + (i / 8 - 16) = i / 8 := by omega
    have : i / 8 - 16 < 16 := by omega
    have : i - 128 < 128 := by omega
    simp [*]
  by_cases h3 : i < 384
  · have e1 : (i - 128 - 128) / 8 = i / 8 - 32 := by omega
    have e2 : (i - 128 - 128) % 8 = i % 8 := by omega
    have e3 : 32 + (i / 8 - 32) = i / 8 := by omega
    have : i / 8 - 32 < 16 := by omega
    have : i - 128 - 128 < 128 := by omega
    have : ¬ (i - 128 < 128) := by omega
    simp [*]
  · have e1 : (i - 128 - 128 - 128) / 8 = i / 8 - 48 := by omega
    have e2 : (i - 128 - 128 - 128) % 8 = i % 8 := by omega
    have e3 : 48 + (i / 8 - 48) = i / 8 := by omega
    have : i / 8 - 48 < 16 := by omega
    have : i - 128 - 128 - 128 < 128 := by omega
    have : ¬ (i - 128 < 128) := by omega
    have : ¬ (i - 128 - 128 < 128) := by omega
    simp [*]

theorem lane2_0 (h l : BitVec 128) : lane (h ++ l) 0 = l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lane, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [hi]

theorem lane2_1 (h l : BitVec 128) : lane (h ++ l) 1 = h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lane, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  have : ¬ (128 * 1 + i < 128) := by omega
  simp [hi, this]

theorem lane4 (a b c d : BitVec 128) :
    lane (a ++ b ++ c ++ d) 0 = d ∧ lane (a ++ b ++ c ++ d) 1 = c ∧
    lane (a ++ b ++ c ++ d) 2 = b ∧ lane (a ++ b ++ c ++ d) 3 = a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply BitVec.eq_of_getLsbD_eq
  all_goals intro i hi
  all_goals simp only [lane, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  · simp [hi]
  · have : ¬ (128 * 1 + i < 128) := by omega
    have : 128 * 1 + i - 128 = i := by omega
    simp [hi, *]
  · have : ¬ (128 * 2 + i < 128) := by omega
    have : ¬ (128 * 2 + i - 128 < 128) := by omega
    have : 128 * 2 + i - 128 - 128 = i := by omega
    simp [hi, *]
  · have : ¬ (128 * 3 + i < 128) := by omega
    have : ¬ (128 * 3 + i - 128 < 128) := by omega
    have : ¬ (128 * 3 + i - 128 - 128 < 128) := by omega
    have : 128 * 3 + i - 128 - 128 - 128 = i := by omega
    simp [hi, *]

theorem perLane2_2 (f : BitVec 128 → BitVec 128 → BitVec 128) (h1 l1 h2 l2 : BitVec 128) :
    perLane2 2 f (h1 ++ l1) (h2 ++ l2) = f h1 h2 ++ f l1 l2 := by
  simp only [perLane2, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.foldl_cons, List.foldl_nil]
  rw [show (h1 ++ l1 : BitVec 256) = h1 ++ l1 from rfl]
  simp only [lane2_0, lane2_1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_zero]
  by_cases hh : i < 128
  · have : i < 256 := by omega
    simp [hh, this]
  · have : i - 128 < 128 := by omega
    have h0 : (f l1 l2).getLsbD i = false := BitVec.getLsbD_of_ge _ i (by omega)
    have : i < 256 := by omega
    have : i - 128 < 256 := by omega
    simp [hh, *]

theorem perLane2_4 (f : BitVec 128 → BitVec 128 → BitVec 128) (a b c d a' b' c' d' : BitVec 128) :
    perLane2 4 f (a ++ b ++ c ++ d) (a' ++ b' ++ c' ++ d') = f a a' ++ f b b' ++ f c c' ++ f d d' := by
  obtain ⟨x0, x1, x2, x3⟩ := lane4 a b c d
  obtain ⟨y0, y1, y2, y3⟩ := lane4 a' b' c' d'
  simp only [perLane2, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.foldl_cons, List.foldl_nil]
  rw [show (a ++ b ++ c ++ d : BitVec 512) = a ++ b ++ c ++ d from rfl]
  simp only [x0, x1, x2, x3, y0, y1, y2, y3]
  clear x0 x1 x2 x3 y0 y1 y2 y3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_zero]
  have g : ∀ (x : BitVec 128) j, 128 ≤ j → x.getLsbD j = false := fun x j h => BitVec.getLsbD_of_ge x j h
  have e512 : i < 512 := by omega
  have q1 : i - 128 < 512 := Nat.lt_of_le_of_lt (Nat.sub_le i 128) e512
  have q2 : i - 256 < 512 := Nat.lt_of_le_of_lt (Nat.sub_le i 256) e512
  have q3 : i - 384 < 512 := Nat.lt_of_le_of_lt (Nat.sub_le i 384) e512
  by_cases h1 : i < 128
  · have a1 : i < 256 := by omega
    have a2 : i < 384 := by omega
    simp only [h1, a1, a2, e512, decide_true, decide_false, Bool.true_and, Bool.not_true,
      Bool.false_and, Bool.or_false, ite_true, Nat.mul_zero, Nat.sub_zero, Nat.not_lt_zero,
      Bool.not_false, Bool.false_or, h1, if_pos, Bool.and_true, Nat.reduceMul]
  by_cases h2 : i < 256
  · have := g (f d d') i (by omega)
    have : i < 384 := by omega
    simp [h1, h2, *]; intro; omega
  by_cases h3 : i < 384
  · have := g (f d d') i (by omega)
    have := g (f c c') (i - 128) (by omega)
    have : ¬ (i - 128 < 128) := by omega
    have : i - 128 - 128 = i - 256 := by omega
    simp [h1, h2, h3, *]; intro; omega
  · have := g (f d d') i (by omega)
    have := g (f c c') (i - 128) (by omega)
    have := g (f b b') (i - 256) (by omega)
    have : ¬ (i - 128 < 128) := by omega
    have : ¬ (i - 128 - 128 < 128) := by omega
    have : i - 128 - 128 - 128 = i - 384 := by omega
    simp [h1, h2, h3, *]

end Crc32fastVerif

namespace Crc32Spec

/-- One 128-bit lane of the AVX2 fold constant (fold by 1024 bits = 128 bytes). -/
def k1024 : BitVec 128 := (0x14a7fe880#64) ++ (0x1e88ef372#64)
/-- One 128-bit lane of the AVX-512 fold constant (fold by 2048 bits = 256 bytes). -/
def k2048 : BitVec 128 := (0x1322d1430#64) ++ (0x11542778a#64)

/- Folding by 128 bytes is two folds by 64 bytes, so it is enough to compare against `k1k2`
   applied twice (this keeps the kernel check shallow). -/
theorem fold128_basis : ∀ j, j < 128 →
    R16 (F k1k2 (F k1k2 (eW 128 j))) = R16 (F k1024 (eW 128 j)) := by
  decide +kernel

theorem fold256_basis : ∀ j, j < 128 →
    R16 (F k1k2 (F k1k2 (F k1k2 (F k1k2 (eW 128 j))))) = R16 (F k2048 (eW 128 j)) := by
  decide +kernel

theorem foldBy128 (a : BitVec 128) : Zn 128 (R16 a) = R16 (F k1024 a) := by
  have h := linW_ext (f := fun x => R16 (F k1k2 (F k1k2 x))) (g := fun x => R16 (F k1024 x))
    (comp_lin R16_lin (fun x y => by
      show F k1k2 (F k1k2 (x ^^^ y)) = F k1k2 (F k1k2 x) ^^^ F k1k2 (F k1k2 y)
      rw [F_xor, F_xor]))
    (comp_lin R16_lin (F_xor k1024)) fold128_basis a
  have e : Zn 128 (R16 a) = Zn 64 (Zn 64 (R16 a)) := by rw [Zn_add]
  rw [e, foldBy64, foldBy64]
  exact h

theorem foldBy256 (a : BitVec 128) : Zn 256 (R16 a) = R16 (F k2048 a) := by
  have h := linW_ext (f := fun x => R16 (F k1k2 (F k1k2 (F k1k2 (F k1k2 x)))))
    (g := fun x => R16 (F k2048 x))
    (comp_lin R16_lin (fun x y => by
      show F k1k2 (F k1k2 (F k1k2 (F k1k2 (x ^^^ y)))) =
        F k1k2 (F k1k2 (F k1k2 (F k1k2 x))) ^^^ F k1k2 (F k1k2 (F k1k2 (F k1k2 y)))
      rw [F_xor, F_xor, F_xor, F_xor]))
    (comp_lin R16_lin (F_xor k2048)) fold256_basis a
  have e : Zn 256 (R16 a) = Zn 64 (Zn 64 (Zn 64 (Zn 64 (R16 a)))) := by rw [Zn_add, Zn_add, Zn_add]
  rw [e, foldBy64, foldBy64, foldBy64, foldBy64]
  exact h

end Crc32Spec

namespace Crc32Spec

/-- Pending 16-byte blocks in increasing offset, as one CRC register value: block `i` of `n`
    still has `16 * (n - 1 - i)` bytes to travel. -/
def SL : List (BitVec 128) → BitVec 32
  | [] => 0#32
  | x :: xs => Zn (16 * xs.length) (R16 x) ^^^ SL xs

theorem SL_cons (x : BitVec 128) (xs : List (BitVec 128)) :
    SL (x :: xs) = Zn (16 * xs.length) (R16 x) ^^^ SL xs := rfl

theorem Zn_zero' (x : BitVec 32) : Zn 0 x = x := rfl

theorem Zn_comm (j k : Nat) (x : BitVec 32) : Zn j (Zn k x) = Zn k (Zn j x) := by
  rw [Zn_add, Zn_add, Nat.add_comm]

theorem Zn_zero_val (k : Nat) : Zn k 0#32 = 0#32 := by
  have h := Zn_xor k 0#32 0#32
  rw [BitVec.xor_self, BitVec.xor_self] at h
  exact h

/-- `SL` of a lane-wise fold: every pending block moves forward by `D` bytes. -/
theorem SL_fold (D : Nat) (K : BitVec 128) (hK : ∀ a, Zn D (R16 a) = R16 (F K a)) :
    ∀ (bs xs : List (BitVec 128)), bs.length = xs.length →
      SL (List.zipWith (fun b x => b ^^^ F K x) bs xs) = Zn D (SL xs) ^^^ SL bs
  | [], [], _ => by simp [SL, Zn_zero_val]
  | b :: bs, x :: xs, h => by
    have hl : bs.length = xs.length := by simpa using h
    have hx : ∀ a c : BitVec 128, R16 (a ^^^ c) = R16 a ^^^ R16 c := R16_lin
    simp only [List.zipWith_cons_cons, SL_cons, List.length_zipWith, hl, Nat.min_self,
      SL_fold D K hK bs xs hl, hx, Zn_xor, ← hK, Zn_comm D]
    ac_rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The serial collapse `x := next ^^^ F k3k4 x` of `reduce128`. -/
theorem SL_collapse : ∀ (rest : List (BitVec 128)) (a : BitVec 128),
    R16 (rest.foldl (fun acc x => x ^^^ F k3k4 acc) a) = SL (a :: rest)
  | [], a => by simp [SL, Zn_zero']
  | x :: r, a => by
    have hx : ∀ a c : BitVec 128, R16 (a ^^^ c) = R16 a ^^^ R16 c := R16_lin
    rw [List.foldl_cons, SL_collapse r, SL_cons, SL_cons, SL_cons, hx, ← foldBy16, Zn_xor, Zn_add,
      List.length_cons]
    rw [show 16 * r.length + 16 = 16 * (r.length + 1) by omega]
    ac_rfl

end Crc32Spec

namespace Crc32fastVerif

/-- The first `m` 16-byte blocks of `l`, as registers. -/
def blks (l : List U8) : Nat → List (BitVec 128)
  | 0 => []
  | m + 1 => blk l :: blks (l.drop 16) m

theorem blks_length (l : List U8) (m : Nat) : (blks l m).length = m := by
  induction m generalizing l with
  | zero => rfl
  | succ m ih => simp [blks, ih]

/-- Consuming `m` blocks at once. -/
theorem stepN (m : Nat) (c : BitVec 32) (l : List U8) (h : 16 * m ≤ l.length) :
    crcRaw c (bytes l) = crcRaw (Zn (16 * m) c ^^^ SL (blks l m)) (bytes (l.drop (16 * m))) := by
  induction m generalizing c l with
  | zero => simp [blks, SL, Zn_zero']
  | succ m ih =>
    rw [step16 c l (by omega), ih _ (l.drop 16) (by simp; omega)]
    simp only [List.drop_drop, blks, SL_cons, blks_length, Zn_xor, Zn_add]
    rw [show 16 * m + 16 = 16 * (m + 1) by omega, show 16 + 16 * m = 16 * (m + 1) by omega]
    ac_rfl

/-- One round of an `n`-stream fold by `16 * n` bytes keeps the CRC of everything consumed. -/
theorem stepFold (K : BitVec 128) (xs : List (BitVec 128))
    (hK : ∀ a, Zn (16 * xs.length) (R16 a) = R16 (F K a)) (l : List U8) (h : 16 * xs.length ≤ l.length) :
    crcRaw (SL xs) (bytes l) =
      crcRaw (SL (List.zipWith (fun b x => b ^^^ F K x) (blks l xs.length) xs))
        (bytes (l.drop (16 * xs.length))) := by
  rw [stepN xs.length _ l h, SL_fold _ K hK _ _ (blks_length _ _)]

end Crc32fastVerif
