/-
  Properties of the pure reference specification (no Aeneas code involved).
-/
module
public import Proofs.Spec
@[expose] public section

namespace percent_encoding.Spec

theorem hexVal_hexDigit (n : Nat) (h : n < 16) : hexVal (hexDigit n) = some n := by
  revert n; decide

theorem hexDigit_lt (n : Nat) (h : n < 16) : hexDigit n < 128 := by
  revert n; decide

theorem encode_append (s : ascii_set.AsciiSet) (x y : List Nat) :
    encode s (x ++ y) = encode s x ++ encode s y := by
  induction x with
  | nil => simp [encode]
  | cons b rest ih => simp [encode, ih]

theorem encode_of_not_should (s : ascii_set.AsciiSet) (x : List Nat)
    (h : ∀ b ∈ x, shouldEncode s b = false) : encode s x = x := by
  induction x with
  | nil => simp [encode]
  | cons b rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [encode, h.1, ih h.2]

theorem decode_cons_of_ne (b : Nat) (y : List Nat) (hb : b ≠ 37) :
    decode (b :: y) = b :: decode y := by
  match y with
  | [] => simp [decode]
  | [c] => simp [decode]
  | c :: d :: rest => rw [decode]; all_goals simp_all

theorem decode_escape (b : Nat) (y : List Nat) (hb : b < 256) :
    decode (encByte b ++ y) = b :: decode y := by
  have h1 : b / 16 < 16 := by omega
  have h2 : b % 16 < 16 := by omega
  simp only [encByte, List.cons_append, List.nil_append]
  rw [decode]
  simp only [hexVal_hexDigit _ h1, hexVal_hexDigit _ h2]
  congr 1
  omega

theorem decode_pct (rest : List Nat) :
    decode (37 :: rest) =
      match afterPct rest with
      | some v => v :: decode (rest.drop 2)
      | none => 37 :: decode rest := by
  match rest with
  | [] => simp [decode, afterPct]
  | [c] => simp [decode, afterPct]
  | h :: l :: r =>
    rw [decode]
    simp only [afterPct, List.drop_succ_cons, List.drop_zero]
    split <;> simp_all

theorem hexVal_lt (c v : Nat) (h : hexVal c = some v) : v < 16 := by
  unfold hexVal at h
  split_ifs at h <;> simp at h <;> omega

/-- **Round trip.** Decoding the encoding gives back the input, provided the
    set encodes `%` itself (true for `NON_ALPHANUMERIC`, false for `CONTROLS`). -/
theorem decode_encode (s : ascii_set.AsciiSet) (x : List Nat)
    (hx : ∀ b ∈ x, b < 256) (hpct : shouldEncode s 37 = true) :
    decode (encode s x) = x := by
  induction x with
  | nil => simp [encode, decode]
  | cons b rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hx
    simp only [encode]
    split
    · rw [decode_escape _ _ hx.1, ih hx.2]
    · rename_i hb
      have : b ≠ 37 := by rintro rfl; simp_all
      simp only [List.singleton_append]
      rw [decode_cons_of_ne _ _ this, ih hx.2]

/-- Upper-case hex digits and `%`: the only characters an escape can produce. -/
def isEscapeChar (c : Nat) : Bool :=
  c == 37 || (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 70)

theorem hexDigit_isEscapeChar (n : Nat) (h : n < 16) : isEscapeChar (hexDigit n) = true := by
  revert n; decide

/-- **Output alphabet.** Every output byte is ASCII, and the only output bytes
    that belong to the set are `%` and upper-case hex digits (from escapes). -/
theorem encode_output_allowed (s : ascii_set.AsciiSet) (x : List Nat)
    (hx : ∀ b ∈ x, b < 256) :
    ∀ c ∈ encode s x, c < 128 ∧ (shouldEncode s c = true → isEscapeChar c = true) := by
  induction x with
  | nil => simp [encode]
  | cons b rest ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hx
    intro c hc
    simp only [encode, List.mem_append] at hc
    rcases hc with hc | hc
    · split at hc
      · have h1 : b / 16 < 16 := by omega
        have h2 : b % 16 < 16 := by omega
        simp only [encByte, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl
        · simp [isEscapeChar]
        · exact ⟨hexDigit_lt _ h1, fun _ => hexDigit_isEscapeChar _ h1⟩
        · exact ⟨hexDigit_lt _ h2, fun _ => hexDigit_isEscapeChar _ h2⟩
      · rename_i hb
        simp only [List.mem_singleton] at hc
        subst hc
        simp only [shouldEncode, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          not_lt, not_or] at hb
        refine ⟨by omega, fun h => ?_⟩
        simp_all [shouldEncode]
    · exact ih hx.2 c hc

end percent_encoding.Spec
