import Crc32fast.SpecLemmas

/-!
# Spec-level facts behind `combine`

* `update c b = Zn |b| c ^^^ crc32 b` for any finished CRC `c` (`update_eq_Zn_xor`):
  so combining needs only "append `|b|` zero bytes", which is `Zn |b|`.
* The Rust code applies `Zn (2^i)` by a carry-less multiply with table entry
  `i mod 32`. `mulSpec_x2n` proves that for every `i`.

Linear maps on 32-bit registers are compared through their 32 basis images,
so every computational check here is small.
-/

namespace Crc32Spec

/-! ## Linearity -/

def IsLin (f : BitVec 32 → BitVec 32) : Prop := ∀ x y, f (x ^^^ y) = f x ^^^ f y

theorem IsLin.map_zero {f} (hf : IsLin f) : f 0#32 = 0#32 := by
  have h := hf 0#32 0#32
  rw [BitVec.xor_self] at h
  rw [BitVec.xor_self] at h
  exact h

theorem Zn_lin (n : Nat) : IsLin (Zn n) := Zn_xor n

theorem Zn_zero (n : Nat) : Zn n 0#32 = 0#32 := (Zn_lin n).map_zero

theorem Zn_comm_Z (n : Nat) (c : BitVec 32) : Zn n (Z c) = Z (Zn n c) := by
  have h1 := Zn_add n 1 c
  have h2 := Zn_add 1 n c
  simp only [Zn] at h1
  exact h1

/-- Feeding bytes splits into "the register, padded with zeros" and "the data,
fed into a zero register". -/
theorem crcRaw_split (c : BitVec 32) (l : List (BitVec 8)) :
    crcRaw c l = Zn l.length c ^^^ crcRaw 0#32 l := by
  induction l generalizing c with
  | nil => simp [crcRaw, Zn]
  | cons b l ih =>
    rw [crcRaw_cons, crcRaw_cons, ih, ih (byteStep 0#32 b), byteStep_split, byteStep_split,
      Z_zero, BitVec.zero_xor, Zn_xor, Zn_comm_Z]
    simp only [List.length_cons, Zn, BitVec.xor_assoc]

theorem not_eq_xor (x : BitVec 32) : ~~~ x = x ^^^ (-1#32) := by bv_bits 32

/-- Continuing a finished CRC `c` with `b` = pad `c` with `|b|` zero bytes, XOR `crc32 b`. -/
theorem update_eq_Zn_xor (c : BitVec 32) (b : List (BitVec 8)) :
    update c b = Zn b.length c ^^^ crc32 b := by
  simp only [crc32, update]
  rw [crcRaw_split (~~~c) b, crcRaw_split (~~~0#32) b]
  rw [not_eq_xor (Zn b.length (~~~c) ^^^ crcRaw 0#32 b), not_eq_xor c,
    not_eq_xor (Zn b.length (~~~0#32) ^^^ crcRaw 0#32 b), not_eq_xor 0#32, Zn_xor, Zn_xor,
    Zn_zero, BitVec.zero_xor]
  ac_rfl

/-! ## Carry-less multiplication, as written in the Rust code -/

/-- `bitStep` applied `i` times: multiplication by `x^i` modulo the polynomial. -/
def bitStepN : Nat → BitVec 32 → BitVec 32
  | 0, b => b
  | i + 1, b => bitStepN i (bitStep b)

/-- The loop of `combine::multiply`, run for `k` more rounds starting at round `i`. -/
def mulLoop (a : BitVec 32) : Nat → Nat → BitVec 32 → BitVec 32 → BitVec 32
  | 0, _, _, p => p
  | k + 1, i, b, p => mulLoop a k (i + 1) (bitStep b) (p ^^^ (if a.getLsbD (31 - i) then b else 0#32))

/-- `multiply(a, b)`: the product of `a` and `b` as polynomials over GF(2), modulo
the CRC polynomial, in bit-reflected form. -/
def mulSpec (a b : BitVec 32) : BitVec 32 := mulLoop a 32 0 b 0#32

theorem mulLoop_lin (a : BitVec 32) (k i : Nat) (b b' p p' : BitVec 32) :
    mulLoop a k i (b ^^^ b') (p ^^^ p') = mulLoop a k i b p ^^^ mulLoop a k i b' p' := by
  induction k generalizing i b b' p p' with
  | zero => rfl
  | succ k ih =>
    simp only [mulLoop, bitStep_xor]
    rw [← ih]
    congr 1
    split <;> ac_rfl

theorem mulSpec_lin (a : BitVec 32) : IsLin (mulSpec a) := by
  intro x y
  simp only [mulSpec]
  rw [← mulLoop_lin, BitVec.xor_self]

/-! ## Linear maps agree when they agree on a basis -/

def e (j : Nat) : BitVec 32 := 1#32 <<< j

/-- Rebuild `x` from its bits. -/
def rebuild (x : BitVec 32) (l : List Nat) (acc : BitVec 32) : BitVec 32 :=
  l.foldl (fun acc j => acc ^^^ (if x.getLsbD j then e j else 0#32)) acc

theorem getLsbD_e (j i : Nat) (hi : i < 32) : (e j).getLsbD i = decide (i = j) := by
  simp only [e, BitVec.getLsbD_shiftLeft]
  by_cases h : i = j
  · subst h; simp [hi]
  · by_cases hlt : i < j
    · simp [h, hlt]
    · have : i - j ≠ 0 := by omega
      simp [h, hlt, BitVec.getLsbD_one, this]

/-- The first `n` bits of `x`, rebuilt one basis vector at a time. -/
def rb (x : BitVec 32) : Nat → BitVec 32
  | 0 => 0#32
  | n + 1 => rb x n ^^^ (if x.getLsbD n then e n else 0#32)

theorem rebuild_range (x : BitVec 32) (n : Nat) : rebuild x (List.range n) 0#32 = rb x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rebuild] at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem getLsbD_rb (x : BitVec 32) (n i : Nat) (hi : i < 32) :
    (rb x n).getLsbD i = (decide (i < n) && x.getLsbD i) := by
  induction n with
  | zero => simp [rb]
  | succ n ih =>
    simp only [rb, BitVec.getLsbD_xor, ih]
    by_cases hx : x.getLsbD n
    · simp only [hx, ite_true, getLsbD_e n i hi]
      by_cases h : i = n
      · subst h; simp [hx]
      · by_cases hlt : i < n <;> simp [h, hlt] <;> omega
    · simp only [hx, Bool.false_eq_true, ite_false, BitVec.getLsbD_zero, Bool.bne_false]
      by_cases h : i = n
      · subst h; simp [hx]
      · by_cases hlt : i < n
        · simp [hlt, show i < n + 1 by omega]
        · simp [hlt, show ¬ i < n + 1 by omega]

theorem rebuild_eq (x : BitVec 32) : rebuild x (List.range 32) 0#32 = x := by
  rw [rebuild_range]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rb x 32 i hi]
  simp [hi]

theorem lin_rebuild {f} (hf : IsLin f) (x : BitVec 32) (l : List Nat) (acc : BitVec 32) :
    f (rebuild x l acc) = l.foldl (fun acc j => acc ^^^ (if x.getLsbD j then f (e j) else 0#32)) (f acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons j l ih =>
    simp only [rebuild, List.foldl] at ih ⊢
    rw [ih, hf]
    congr 2
    split
    · rfl
    · exact hf.map_zero

theorem lin_ext {f g} (hf : IsLin f) (hg : IsLin g) (h : ∀ j, j < 32 → f (e j) = g (e j)) :
    ∀ x, f x = g x := by
  intro x
  rw [← rebuild_eq x, lin_rebuild hf, lin_rebuild hg, hf.map_zero, hg.map_zero]
  have : ∀ (l : List Nat), (∀ j ∈ l, j < 32) → ∀ acc,
      l.foldl (fun acc j => acc ^^^ (if x.getLsbD j then f (e j) else 0#32)) acc =
      l.foldl (fun acc j => acc ^^^ (if x.getLsbD j then g (e j) else 0#32)) acc := by
    intro l hl
    induction l with
    | nil => intro acc; rfl
    | cons j l ih =>
      intro acc
      simp only [List.foldl]
      rw [h j (hl j (by simp))]
      exact ih (fun k hk => hl k (by simp [hk])) _
  exact this _ (fun j hj => by simpa using hj) _

/-! ## The 32 table constants -/

/-- `X2N_TABLE` from `combine.rs`. Entry `k` represents `x^(2^k * 8)` mod P. -/
def x2n : List (BitVec 32) :=
  [0x00800000, 0x00008000, 0xedb88320, 0xb1e6b092, 0xa06a2517, 0xed627dae, 0x88d14467, 0xd7bbfe6a,
   0xec447f11, 0x8e7ea170, 0x6427800e, 0x4d47bae0, 0x09fe548f, 0x83852d0f, 0x30362f1a, 0x7b5a9cc3,
   0x31fec169, 0x9fec022a, 0x6c8dedc4, 0x15d6874d, 0x5fde7a4e, 0xbad90e37, 0x2e4e5eef, 0x4eaba214,
   0xa8a472c0, 0x429a969e, 0x148d302a, 0xc40ba6d0, 0xc4e22c3c, 0x40000000, 0x20000000, 0x08000000]

/-- Entry 0 multiplies by `x^8`, i.e. appends one zero byte. -/
theorem x2n_zero_basis : ∀ j, j < 32 → mulSpec (x2n[0]!) (e j) = Z (e j) := by
  decide +kernel

/-- Squaring entry `k` gives entry `k+1`, and squaring entry 31 wraps to entry 0. -/
theorem x2n_square_basis : ∀ k, k < 32 → ∀ j, j < 32 →
    mulSpec (x2n[(k + 1) % 32]!) (e j) = mulSpec (x2n[k]!) (mulSpec (x2n[k]!) (e j)) := by
  decide +kernel

theorem Zn_two_pow_succ (i : Nat) (c : BitVec 32) : Zn (2 ^ (i + 1)) c = Zn (2 ^ i) (Zn (2 ^ i) c) := by
  rw [Zn_add, Nat.pow_succ, Nat.mul_two]

theorem lin_comp {f g} (hf : IsLin f) (hg : IsLin g) : IsLin (fun x => f (g x)) := by
  intro x y; simp only []; rw [hg x y, hf]

/-- Multiplying by table entry `i mod 32` appends `2^i` zero bytes, for every `i`. -/
theorem mulSpec_x2n (i : Nat) (c : BitVec 32) : mulSpec (x2n[i % 32]!) c = Zn (2 ^ i) c := by
  induction i generalizing c with
  | zero =>
    exact lin_ext (mulSpec_lin _) (Zn_lin 1) (fun j hj => by simpa [Zn] using x2n_zero_basis j hj) c
  | succ i ih =>
    rw [Zn_two_pow_succ, ← ih, ← ih]
    have hk : i % 32 < 32 := Nat.mod_lt _ (by decide)
    have hmod : (i + 1) % 32 = (i % 32 + 1) % 32 := by omega
    rw [hmod]
    exact lin_ext (mulSpec_lin _) (lin_comp (mulSpec_lin _) (mulSpec_lin _))
      (fun j hj => x2n_square_basis (i % 32) hk j hj) c

end Crc32Spec
