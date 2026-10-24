import SemverModel.Proofs.RefineVersion
/-! Round trips between `parseM` and `printM`. -/
open Aeneas Aeneas.Std
open semver_model SemverSpec

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace SemverProofs

/-! ## Decimal digits -/

def digitB (d : Nat) (h : d < 10) : U8 := UScalar.ofNat (48 + d) (by scalar_tac)

theorem decimal_lt10 (n : Nat) (h : n < 10) : decimal n = [UScalar.ofNat (48 + n % 10) (by
      have := Nat.mod_lt n (by decide : 10 > 0); scalar_tac)] := by
  rw [decimal_unfold]; simp [show ¬ n ≥ 10 by omega]

theorem ofNat_congr (a b : Nat) (ha : a ≤ UScalar.cMax .U8) (hb : b ≤ UScalar.cMax .U8) (h : a = b) :
    (UScalar.ofNat a ha : U8) = UScalar.ofNat b hb := by subst h; rfl

theorem decimal_snoc (v dd : Nat) (hv : 1 ≤ v) (hd : dd < 10) :
    decimal (v * 10 + dd) = decimal v ++ [UScalar.ofNat (48 + dd) (by scalar_tac)] := by
  rw [decimal_unfold]
  have h1 : v * 10 + dd ≥ 10 := by omega
  have h2 : (v * 10 + dd) / 10 = v := by omega
  have h3 : (v * 10 + dd) % 10 = dd := by omega
  simp only [h1, ite_true, h2]
  exact congrArg (fun x => decimal v ++ [x]) (ofNat_congr _ _ (by scalar_tac) (by scalar_tac) (by omega))

theorem digit_byte (d : U8) (h : isDig d = true) :
    (UScalar.ofNat (48 + (d.val - 48)) (by unfold isDig at h; simp at h; scalar_tac) : U8) = d := by
  unfold isDig at h; simp at h
  rw [UScalar.eq_equiv]
  simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq]
  (try simp); omega

theorem sub_one (l : List U8) (k : Nat) (h : k < l.length) : sub l k (k + 1) = [l[k]] := by
  rw [sub_succ l k k (Nat.le_refl _) h, sub_self]; rfl

theorem sub_append (l : List U8) (a k e : Nat) (h1 : a ≤ k) (h2 : k ≤ e) (h3 : e ≤ l.length) :
    sub l a e = sub l a k ++ sub l k e := by
  unfold sub
  have ht : (l.take e).take k = l.take k := by rw [List.take_take, Nat.min_eq_left h2]
  conv => lhs; rw [← List.take_append_drop k (l.take e)]
  rw [List.drop_append_of_le_length (by simp; omega), ht]

/-! ## What a successful number parse read -/

theorem numLoop_read (s : List U8) (st : Nat) (pos : Position) (len v a e : Nat)
    (h : numLoop s st pos len v = .Ok (a, e))
    (hi : (len = 0 ∧ v = 0) ∨ (0 < len ∧ st + len ≤ s.length ∧ sub s st (st + len) = decimal v)) :
    st < e ∧ e ≤ s.length ∧ sub s st e = decimal a := by
  revert h hi
  fun_induction numLoop s st pos len v <;> intro h hi <;> (try simp at h)
  · obtain ⟨rfl, rfl⟩ := h
    rcases hi with ⟨_, _⟩ | ⟨_, hb, hs⟩
    · omega
    · exact ⟨by omega, hb, hs⟩
  · rename_i len v hk d hd hz ho1 ho2 ih
    apply ih h
    right
    have hdig : isDig d = true := by unfold isDig; simp; omega
    refine ⟨by omega, by omega, ?_⟩
    rw [show st + (len + 1) = st + len + 1 by omega, sub_succ s st (st + len) (by omega) hk]
    have hdd : s[st + len] = d := rfl
    rw [hdd]
    have hdl : d.val - 48 < 10 := by unfold isDig at hdig; simp at hdig; omega
    rcases hi with ⟨rfl, rfl⟩ | ⟨hl, _, hs⟩
    · simp only [Nat.add_zero, sub_self, List.nil_append, Nat.zero_mul, Nat.zero_add]
      rw [decimal_lt10 _ hdl]
      congr 1
      rw [UScalar.eq_equiv]
      simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq]
      unfold isDig at hdig; simp at hdig
      (try simp); omega
    · have hv : 1 ≤ v := by omega
      rw [hs, decimal_snoc v (d.val - 48) hv hdl]
      congr 2
      exact (digit_byte d hdig).symm
  · obtain ⟨rfl, rfl⟩ := h
    rcases hi with ⟨_, _⟩ | ⟨_, hb, hs⟩
    · omega
    · exact ⟨by omega, hb, hs⟩

theorem numM_read (s : List U8) (st : Nat) (pos : Position) (a e : Nat) (h : numM s st pos = .Ok (a, e)) :
    st < e ∧ e ≤ s.length ∧ sub s st e = decimal a :=
  numLoop_read s st pos 0 0 a e h (Or.inl ⟨rfl, rfl⟩)

theorem dotM_read (s : List U8) (st : Nat) (pos : Position) (e : Nat) (h : dotM s st pos = .Ok e) :
    e = st + 1 ∧ st < s.length ∧ sub s st e = [DOT] := by
  unfold dotM at h
  split_ifs at h with h1 h2
  simp only [core.result.Result.Ok.injEq] at h
  subst h
  refine ⟨rfl, h1, ?_⟩
  rw [sub_one s st h1, h2]

theorem identM_read (s : List U8) (st : Nat) (isPre : Bool) (e : Nat) (h : identM s st isPre = .Ok e)
    (hb : st ≤ s.length) : st ≤ e ∧ e ≤ s.length :=
  identLoop_bounds s st isPre _ 0 0 false e h (by simpa using hb)

theorem byte_at (s : List U8) (k : Nat) (b : U8) (hk : k < s.length) (h : s[k]! = b) :
    sub s k (k + 1) = [b] := by
  rw [sub_one s k hk]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk] at h
  rw [h]

theorem sub_len_ne (s : List U8) (a e : Nat) (h1 : a < e) (h2 : e ≤ s.length) : (sub s a e).length ≠ 0 := by
  rw [sub_length s a e h2]; omega

/-- Parse then print: whatever `parseM` accepts, `printM` gives back byte for byte. -/
theorem parse_print (s : List U8) (v : PVersion) (h : parseM s = .Ok v) : printM v = s := by
  unfold parseM at h
  split_ifs at h with h0
  rcases hM : numM s 0 .Major with ⟨M, k1⟩ | e <;> rw [hM] at h <;> (try simp only [reduceCtorEq] at h)
  obtain ⟨_, hk1, sM⟩ := numM_read _ _ _ _ _ hM
  rcases hD1 : dotM s k1 .Major with k2 | e <;> rw [hD1] at h <;> (try simp only [reduceCtorEq] at h)
  obtain ⟨rfl, _, sD1⟩ := dotM_read _ _ _ _ hD1
  rcases hm : numM s (k1 + 1) .Minor with ⟨m, k3⟩ | e <;> rw [hm] at h <;> (try simp only [reduceCtorEq] at h)
  obtain ⟨_, hk3, sm⟩ := numM_read _ _ _ _ _ hm
  rcases hD2 : dotM s k3 .Minor with k4 | e <;> rw [hD2] at h <;> (try simp only [reduceCtorEq] at h)
  obtain ⟨rfl, _, sD2⟩ := dotM_read _ _ _ _ hD2
  rcases hp : numM s (k3 + 1) .Patch with ⟨p, k5⟩ | e <;> rw [hp] at h <;> (try simp only [reduceCtorEq] at h)
  obtain ⟨_, hk5, sp⟩ := numM_read _ _ _ _ _ hp
  -- the numeric prefix
  have hpre : sub s 0 k5 = decimal M ++ [DOT] ++ decimal m ++ [DOT] ++ decimal p := by
    rw [sub_append s 0 k1 k5 (by omega) (by omega) hk5, sM,
        sub_append s k1 (k1 + 1) k5 (by omega) (by omega) hk5, sD1,
        sub_append s (k1 + 1) k3 k5 (by omega) (by omega) hk5, sm,
        sub_append s k3 (k3 + 1) k5 (by omega) (by omega) hk5, sD2, sp]
    simp
  have hfull : s = sub s 0 k5 ++ sub s k5 s.length := by
    rw [← sub_append s 0 k5 s.length (by omega) hk5 (Nat.le_refl _), sub_zero_full]
  by_cases hend : k5 = s.length
  · simp only [hend, ite_true, core.result.Result.Ok.injEq] at h; subst h
    rw [hfull, hpre, hend, sub_self]; simp [printM]
  simp only [hend, ite_false] at h
  have hk5l : k5 < s.length := by omega
  by_cases hdash : s[k5]! = 45#u8
  · simp only [hdash, ite_true] at h
    rcases hI : identM s (k5 + 1) true with e | err <;> simp only [hI, reduceCtorEq] at h
    obtain ⟨he1, he2⟩ := identM_read s (k5 + 1) true e hI (by omega)
    by_cases hne : e = k5 + 1
    · simp [hne] at h
    simp only [hne, ite_false] at h
    by_cases hplus : e < s.length ∧ s[e]! = 43#u8
    · simp only [hplus, and_self, ite_true] at h
      rcases hB : identM s (e + 1) false with e' | err <;> simp only [hB, reduceCtorEq] at h
      obtain ⟨he1', he2'⟩ := identM_read s (e + 1) false e' hB (by omega)
      by_cases hne' : e' = e + 1
      · simp [hne'] at h
      simp only [hne', ite_false] at h
      by_cases hlt : e' < s.length
      · simp [hlt] at h
      simp only [hlt, ite_false, core.result.Result.Ok.injEq] at h
      subst h
      have he' : e' = s.length := by omega
      subst he'
      conv_rhs => rw [hfull, hpre,
        sub_append s k5 (k5 + 1) s.length (by omega) (by omega) (Nat.le_refl _), byte_at s k5 45#u8 hk5l hdash,
        sub_append s (k5 + 1) e s.length (by omega) (by omega) (Nat.le_refl _),
        sub_append s e (e + 1) s.length (by omega) (by omega) (Nat.le_refl _), byte_at s e 43#u8 hplus.1 hplus.2]
      simp [printM, sub_len_ne s (k5 + 1) e (by omega) he2, sub_len_ne s (e + 1) s.length (by omega) (Nat.le_refl _)]
    · simp only [hplus, ite_false] at h
      by_cases hlt : e < s.length
      · simp [hlt] at h
      simp only [hlt, ite_false, core.result.Result.Ok.injEq] at h
      subst h
      have he : e = s.length := by omega
      subst he
      conv_rhs => rw [hfull, hpre,
        sub_append s k5 (k5 + 1) s.length (by omega) (by omega) (Nat.le_refl _), byte_at s k5 45#u8 hk5l hdash]
      simp [printM, sub_len_ne s (k5 + 1) s.length (by omega) he2]
  · simp only [hdash, ite_false] at h
    by_cases hplus : k5 < s.length ∧ s[k5]! = 43#u8
    · simp only [hplus, and_self, ite_true] at h
      rcases hB : identM s (k5 + 1) false with e' | err <;> simp only [hB, reduceCtorEq] at h
      obtain ⟨he1', he2'⟩ := identM_read s (k5 + 1) false e' hB (by omega)
      by_cases hne' : e' = k5 + 1
      · simp [hne'] at h
      simp only [hne', ite_false] at h
      by_cases hlt : e' < s.length
      · simp [hlt] at h
      simp only [hlt, ite_false, core.result.Result.Ok.injEq] at h
      subst h
      have he' : e' = s.length := by omega
      subst he'
      conv_rhs => rw [hfull, hpre,
        sub_append s k5 (k5 + 1) s.length (by omega) (by omega) (Nat.le_refl _), byte_at s k5 43#u8 hplus.1 hplus.2]
      simp [printM, sub_len_ne s (k5 + 1) s.length (by omega) he2']
    · have hp43 : ¬ s[k5]! = 43#u8 := fun h' => hplus ⟨hk5l, h'⟩
      simp only [hk5l, hp43, and_false, true_and, ite_false, ite_true, reduceCtorEq] at h

/-! ## Reading printed numbers back -/

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  rw [decimal_unfold]; simp

theorem decimal_isDig (n : Nat) : ∀ b ∈ decimal n, isDig b = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [decimal_unfold]
  intro b hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | hb
  · split at hb
    · exact ih (n / 10) (by omega) b hb
    · simp at hb
  · subst hb; unfold isDig
    have := Nat.mod_lt n (by decide : 10 > 0)
    simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq]; simp; omega

theorem numLoop_step (s : List U8) (st : Nat) (pos : Position) (len val : Nat) (hk : st + len < s.length)
    (hd : isDig s[st + len] = true) (hz : ¬(val = 0 ∧ len > 0)) (hov : val * 10 + (s[st + len].val - 48) ≤ U64MAX) :
    numLoop s st pos len val = numLoop s st pos (len + 1) (val * 10 + (s[st + len].val - 48)) := by
  rw [numLoop_unfold]
  unfold isDig at hd; simp at hd
  simp only [hk, _root_.dite_true]
  have h1 : ¬ (s[st + len].val < 48 ∨ s[st + len].val > 57) := by omega
  have h2 : ¬ val * 10 > U64MAX := by omega
  have h3 : ¬ val * 10 + (s[st + len].val - 48) > U64MAX := by omega
  simp only [h1, hz, h2, h3, ite_false]

theorem numLoop_stop (s : List U8) (st : Nat) (pos : Position) (len val : Nat) (hl : 0 < len)
    (hend : st + len = s.length ∨ ∃ h : st + len < s.length, isDig s[st + len] = false) :
    numLoop s st pos len val = .Ok (val, st + len) := by
  rw [numLoop_unfold]
  rcases hend with he | ⟨hk, hd⟩
  · have : ¬ st + len < s.length := by omega
    simp [this, hl]
  · unfold isDig at hd; simp at hd
    have h1 : s[st + len].val < 48 ∨ s[st + len].val > 57 := by omega
    simp [hk, h1, hl]

theorem get_mid (s X C : List U8) (d : U8) (hs : s = X ++ d :: C) (i : Nat) (hi : i = X.length) :
    ∃ h : i < s.length, s[i] = d := by
  subst hs hi; simp

theorem decimal_split (m : Nat) : ∃ d : U8, d.val = 48 + m % 10 ∧
    decimal m = (if m ≥ 10 then decimal (m / 10) else []) ++ [d] :=
  ⟨_, by have := Nat.mod_lt m (by decide : 10 > 0); simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq]; (try simp); (try omega),
   decimal_unfold m⟩

theorem numLoop_dec (s : List U8) (st : Nat) (pos : Position) (m : Nat) :
    ∀ (A C : List U8) (len val : Nat), s = A ++ decimal m ++ C → A.length = st + len →
      ¬(val = 0 ∧ len > 0) → val * 10 ^ (decimal m).length + m ≤ U64MAX →
      numLoop s st pos len val = numLoop s st pos (len + (decimal m).length) (val * 10 ^ (decimal m).length + m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A C len val hs hA hz hov
  obtain ⟨d, hdv, hdm⟩ := decimal_split m
  have hmod := Nat.mod_lt m (by decide : 10 > 0)
  have hdig : isDig d = true := by unfold isDig; simp; omega
  have hdval : d.val - 48 = m % 10 := by omega
  by_cases hm : m ≥ 10
  · simp only [hm, ite_true] at hdm
    have hlen : (decimal m).length = (decimal (m / 10)).length + 1 := by rw [hdm]; simp
    generalize hL : (decimal (m / 10)).length = L at hlen
    have hpos : 1 ≤ m / 10 := by omega
    have hpow : val * 10 ^ (L + 1) = val * 10 ^ L * 10 := by rw [Nat.pow_succ, Nat.mul_assoc]
    rw [hlen, hpow] at hov ⊢
    have hih := ih (m / 10) (by omega) A (d :: C) len val (by rw [hs, hdm]; simp) hA hz
    rw [hL] at hih
    generalize hP : val * 10 ^ L = P at hov hih ⊢
    rw [hih (by omega)]
    obtain ⟨hk, hget⟩ := get_mid s (A ++ decimal (m / 10)) C d (by rw [hs, hdm]; simp) (st + (len + L))
      (by simp [hA, hL]; omega)
    rw [numLoop_step s st pos (len + L) _ hk (by rw [hget]; exact hdig) (by omega) (by rw [hget]; omega)]
    rw [hget, hdval]
    congr 1 <;> omega
  · simp only [hm, ite_false, List.nil_append] at hdm
    have hlen : (decimal m).length = 1 := by rw [hdm]; simp
    rw [hlen] at hov ⊢
    obtain ⟨hk, hget⟩ := get_mid s A C d (by rw [hs, hdm]; simp) (st + len) (by omega)
    rw [numLoop_step s st pos len val hk (by rw [hget]; exact hdig) hz (by rw [hget]; omega)]
    rw [hget, hdval, Nat.mod_eq_of_lt (by omega : m < 10)]; simp

theorem numM_dec (s A C : List U8) (pos : Position) (m : Nat) (hs : s = A ++ decimal m ++ C)
    (hm : m ≤ U64MAX) (hC : C = [] ∨ ∃ c t, C = c :: t ∧ isDig c = false) :
    numM s A.length pos = .Ok (m, A.length + (decimal m).length) := by
  unfold numM
  rw [numLoop_dec s A.length pos m A C 0 0 hs (by simp) (by simp) (by simpa using hm)]
  simp only [Nat.zero_mul, Nat.zero_add]
  apply numLoop_stop _ _ _ _ _ (by have := decimal_ne_nil m; cases h : decimal m <;> simp_all)
  rcases hC with rfl | ⟨c, t, rfl, hc⟩
  · left; simp [hs]
  · right
    obtain ⟨hk, hget⟩ := get_mid s (A ++ decimal m) t c (by simp [hs]) (A.length + (decimal m).length) (by simp)
    exact ⟨hk, by rw [hget]; exact hc⟩

/-! ## Reading printed identifiers back -/

def shiftR (n : Nat) : Res Nat → Res Nat
  | .Ok e => .Ok (n + e)
  | .Err e => .Err e

def Stopper (C : List U8) : Prop :=
  C = [] ∨ ∃ c t, C = c :: t ∧ isIdentNonDigit c = false ∧ isDig c = false ∧ c ≠ DOT

theorem getElem!_mid (A p C : List U8) (i : Nat) (h : i < p.length) :
    (A ++ p ++ C)[A.length + i]! = p[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left h]

theorem identLoop_ctx (A p C : List U8) (isPre : Bool) (pos : Position) (hC : Stopper C) :
    ∀ n acc seg nd, p.length - (acc + seg) = n → acc + seg ≤ p.length →
      identLoop (A ++ p ++ C) A.length isPre pos acc seg nd =
        shiftR A.length (identLoop p 0 isPre pos acc seg nd) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro acc seg nd hn hb
  have hlz : (isPre ∧ seg > 1 ∧ nd = false ∧ (A ++ p ++ C)[A.length + acc]! = 48#u8) ↔
      (isPre ∧ seg > 1 ∧ nd = false ∧ p[0 + acc]! = 48#u8) := by
    by_cases hs : seg > 1
    · rw [getElem!_mid A p C acc (by omega), Nat.zero_add]
    · simp [hs]
  rw [identLoop_unfold (A ++ p ++ C), identLoop_unfold p]
  dsimp only
  simp only [hlz]
  by_cases hk : acc + seg < p.length
  · have hk1 : A.length + acc + seg < (A ++ p ++ C).length := by simp; omega
    have hk2 : 0 + acc + seg < p.length := by omega
    have hget : (A ++ p ++ C)[A.length + acc + seg] = p[0 + acc + seg] := by
      simp only [List.append_assoc]
      rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
      congr 1; omega
    simp only [hk1, hk2, _root_.dite_true, hget]
    split_ifs <;>
      (first
        | exact ih _ (by omega) _ _ _ rfl (by omega)
        | (simp [shiftR]; done)
        | (simp [shiftR]; omega))
  · have hk2 : ¬ 0 + acc + seg < p.length := by omega
    simp only [hk2, _root_.dite_false]
    rcases hC with rfl | ⟨c, t, rfl, hc1, hc2, hc3⟩
    · have hk1 : ¬ A.length + acc + seg < (A ++ p ++ []).length := by simp; omega
      simp only [hk1, _root_.dite_false]
      split_ifs <;> simp [shiftR] <;> omega
    · have hk1 : A.length + acc + seg < (A ++ p ++ c :: t).length := by simp; omega
      have hget : (A ++ p ++ c :: t)[A.length + acc + seg] = c := by
        obtain ⟨_, h⟩ := get_mid (A ++ p ++ c :: t) (A ++ p) t c (by simp) (A.length + acc + seg) (by simp; omega)
        exact h
      simp only [hk1, _root_.dite_true, hget, hc1, hc2, hc3, Bool.false_eq_true, ite_false]
      split_ifs <;> simp [shiftR] <;> omega

/-! ## Print then parse -/

theorem numM_at (s A C : List U8) (pos : Position) (m k : Nat) (hs : s = A ++ decimal m ++ C) (hk : k = A.length)
    (hm : m ≤ U64MAX) (hC : C = [] ∨ ∃ c t, C = c :: t ∧ isDig c = false) :
    numM s k pos = .Ok (m, k + (decimal m).length) := by
  subst hk; exact numM_dec s A C pos m hs hm hC

theorem dotM_at (s X Y : List U8) (pos : Position) (k : Nat) (hs : s = X ++ DOT :: Y) (hk : k = X.length) :
    dotM s k pos = .Ok (k + 1) := by
  obtain ⟨h1, h2⟩ := get_mid s X Y DOT hs k hk
  unfold dotM; simp [h1, h2]

theorem getElem!_at (s X Y : List U8) (b : U8) (k : Nat) (hs : s = X ++ b :: Y) (hk : k = X.length) :
    s[k]! = b := by
  obtain ⟨h1, h2⟩ := get_mid s X Y b hs k hk
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1, h2]

theorem sub_at (s A p C : List U8) (k : Nat) (hs : s = A ++ p ++ C) (hk : k = A.length) :
    sub s k (k + p.length) = p := by
  subst hs hk; unfold sub
  rw [List.take_append_of_le_length (by simp)]
  have : (A ++ p).length = A.length + p.length := by simp
  rw [← this, List.take_length]
  simp

theorem identM_whole (p : List U8) (isPre : Bool) (h : identWholeM p isPre = .Ok p) :
    identM p 0 isPre = .Ok p.length := by
  unfold identWholeM at h
  split at h
  · simp at h
  · rename_i e he; split_ifs at h with h1; subst h1; exact he

theorem identM_at (s A p C : List U8) (isPre : Bool) (k : Nat) (hs : s = A ++ p ++ C) (hk : k = A.length)
    (hC : Stopper C) (h : identWholeM p isPre = .Ok p) :
    identM s k isPre = .Ok (k + p.length) := by
  have hw := identM_whole p isPre h
  unfold identM at hw ⊢
  subst hs hk
  rw [identLoop_ctx A p C isPre _ hC _ 0 0 false rfl (by simp), hw]; rfl

theorem stopper_nil : Stopper [] := Or.inl rfl
theorem stopper_plus (t : List U8) : Stopper (43#u8 :: t) :=
  Or.inr ⟨_, t, rfl, by unfold isIdentNonDigit; decide, by unfold isDig; decide, by decide⟩
theorem nd_dot (t : List U8) : (DOT :: t) = [] ∨ ∃ c u, DOT :: t = c :: u ∧ isDig c = false :=
  Or.inr ⟨_, t, rfl, by unfold isDig; decide⟩
theorem nd_dash (t : List U8) : (45#u8 :: t) = [] ∨ ∃ c u, 45#u8 :: t = c :: u ∧ isDig c = false :=
  Or.inr ⟨_, t, rfl, by unfold isDig; decide⟩
theorem nd_plus (t : List U8) : (43#u8 :: t) = [] ∨ ∃ c u, 43#u8 :: t = c :: u ∧ isDig c = false :=
  Or.inr ⟨_, t, rfl, by unfold isDig; decide⟩
theorem nd_nil : ([] : List U8) = [] ∨ ∃ c u, ([] : List U8) = c :: u ∧ isDig c = false := Or.inl rfl

theorem prefix_parse (M m p : Nat) (R : List U8) (hM : M ≤ U64MAX) (hm : m ≤ U64MAX) (hp : p ≤ U64MAX)
    (hR : R = [] ∨ ∃ c u, R = c :: u ∧ isDig c = false) :
    let S := decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ R))
    let K1 := 0 + (decimal M).length
    let K3 := K1 + 1 + (decimal m).length
    let K5 := K3 + 1 + (decimal p).length
    numM S 0 .Major = .Ok (M, K1) ∧ dotM S K1 .Major = .Ok (K1 + 1) ∧
    numM S (K1 + 1) .Minor = .Ok (m, K3) ∧ dotM S K3 .Minor = .Ok (K3 + 1) ∧
    numM S (K3 + 1) .Patch = .Ok (p, K5) ∧ S.length = K5 + R.length := by
  intro S K1 K3 K5
  refine ⟨numM_at S [] (DOT :: (decimal m ++ DOT :: (decimal p ++ R))) .Major M 0 (by simp [S]) rfl hM (nd_dot _),
    dotM_at S (decimal M) (decimal m ++ DOT :: (decimal p ++ R)) .Major K1 (by simp [S]) (by simp [K1]),
    numM_at S (decimal M ++ [DOT]) (DOT :: (decimal p ++ R)) .Minor m (K1 + 1) (by simp [S]) (by simp [K1]) hm (nd_dot _),
    dotM_at S (decimal M ++ DOT :: decimal m) (decimal p ++ R) .Minor K3 (by simp [S]) (by simp [K3, K1]; omega),
    numM_at S (decimal M ++ DOT :: decimal m ++ [DOT]) R .Patch p (K3 + 1) (by simp [S]) (by simp [K3, K1]; omega) hp hR,
    by simp [S, K5, K3, K1]; omega⟩

/-- A version whose numbers fit in `u64` and whose prerelease and build are each
accepted on their own prints to text that parses back to the same version. -/
theorem print_parse (v : PVersion) (hM : v.major ≤ U64MAX) (hm : v.minor ≤ U64MAX) (hp : v.patch ≤ U64MAX)
    (hpre : identWholeM v.pre true = .Ok v.pre) (hbuild : identWholeM v.build false = .Ok v.build) :
    parseM (printM v) = .Ok v := by
  obtain ⟨M, m, p, pre, build⟩ := v
  simp only at hM hm hp hpre hbuild
  have hS : printM ⟨M, m, p, pre, build⟩ = decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++
      ((if pre.length ≠ 0 then 45#u8 :: pre else []) ++ (if build.length ≠ 0 then 43#u8 :: build else [])))) := by
    simp [printM]
  rw [hS]
  have hne : (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++
      ((if pre.length ≠ 0 then 45#u8 :: pre else []) ++ (if build.length ≠ 0 then 43#u8 :: build else []))))).length ≠ 0 := by
    simp
  by_cases hp0 : pre.length = 0 <;> by_cases hb0 : build.length = 0
  · have hpe : pre = [] := List.eq_nil_of_length_eq_zero hp0
    have hbe : build = [] := List.eq_nil_of_length_eq_zero hb0
    subst hpe hbe
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := prefix_parse M m p [] hM hm hp nd_nil
    simp only [hp0, hb0, ne_eq, not_true_eq_false, ite_false, List.append_nil] at f1 f2 f3 f4 f5 f6 hne ⊢
    unfold parseM
    simp only [hne, ite_false, f1, f2, f3, f4, f5, f6, List.length_nil, Nat.add_zero, ite_true]
    split_ifs <;> first | rfl | omega
  all_goals (
    have hpL : (decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)).length =
        0 + (decimal M).length + 1 + (decimal m).length + 1 + (decimal p).length := by simp; omega)
  · -- build only
    have hpe : pre = [] := List.eq_nil_of_length_eq_zero hp0
    subst hpe
    simp only [hb0, ne_eq, not_true_eq_false, not_false_eq_true, ite_false, ite_true, List.nil_append,
      List.length_nil] at hne ⊢
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := prefix_parse M m p (43#u8 :: build) hM hm hp (nd_plus _)
    generalize (0 + (decimal M).length + 1 + (decimal m).length + 1 + (decimal p).length) = K5 at f5 f6 hpL
    have hb1 : 0 < build.length := by omega
    simp only [List.length_cons] at f6
    have hK5ne : ¬ K5 = (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 43#u8 :: build))).length := by omega
    have hlt : K5 < (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 43#u8 :: build))).length := by omega
    have g43 := getElem!_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 43#u8 :: build)))
      (decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) build 43#u8 K5 (by simp) hpL.symm
    have iB := identM_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 43#u8 :: build)))
      (decimal M ++ DOT :: (decimal m ++ DOT :: decimal p) ++ [43#u8]) build [] false (K5 + 1)
      (by simp) (by simp at hpL ⊢; omega) stopper_nil hbuild
    have sB := sub_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 43#u8 :: build)))
      (decimal M ++ DOT :: (decimal m ++ DOT :: decimal p) ++ [43#u8]) build [] (K5 + 1)
      (by simp) (by simp at hpL ⊢; omega)
    have hne2 : ¬ K5 + 1 + build.length = K5 + 1 := by omega
    have hfin : ¬ K5 + 1 + build.length < (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 43#u8 :: build))).length := by omega
    have h4345 : ¬ (43#u8 : U8) = 45#u8 := by decide
    unfold parseM
    simp only [hne, ite_false, f1, f2, f3, f4, f5, hK5ne, g43, h4345, hlt, and_self, ite_true, iB, hne2, sB, hfin]
  · -- prerelease only
    have hbe : build = [] := List.eq_nil_of_length_eq_zero hb0
    subst hbe
    simp only [hp0, ne_eq, not_true_eq_false, not_false_eq_true, ite_false, ite_true, List.append_nil,
      List.length_nil] at hne ⊢
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := prefix_parse M m p (45#u8 :: pre) hM hm hp (nd_dash _)
    generalize (0 + (decimal M).length + 1 + (decimal m).length + 1 + (decimal p).length) = K5 at f5 f6 hpL
    have hb1 : 0 < pre.length := by omega
    simp only [List.length_cons] at f6
    have hK5ne : ¬ K5 = (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: pre))).length := by omega
    have g45 := getElem!_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: pre))) (decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) pre 45#u8 K5 (by simp) hpL.symm
    have iP := identM_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: pre))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ [45#u8]) pre [] true (K5 + 1)
      (by simp) (by simp at hpL ⊢; omega) stopper_nil hpre
    have sP := sub_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: pre))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ [45#u8]) pre [] (K5 + 1) (by simp) (by simp at hpL ⊢; omega)
    have hne2 : ¬ K5 + 1 + pre.length = K5 + 1 := by omega
    have hfin : ¬ K5 + 1 + pre.length < (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: pre))).length := by omega
    unfold parseM
    simp only [hne, ite_false, f1, f2, f3, f4, f5, hK5ne, g45, ite_true, iP, hne2, sP, hfin, false_and]
  · -- both
    simp only [hp0, hb0, ne_eq, not_false_eq_true, ite_true, List.cons_append] at hne ⊢
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := prefix_parse M m p (45#u8 :: (pre ++ 43#u8 :: build)) hM hm hp (nd_dash _)
    generalize (0 + (decimal M).length + 1 + (decimal m).length + 1 + (decimal p).length) = K5 at f5 f6 hpL
    have hb1 : 0 < pre.length := by omega
    have hb2 : 0 < build.length := by omega
    have f6' : (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))).length = K5 + 1 + pre.length + 1 + build.length := by rw [f6]; simp; omega
    clear f6
    have hK5ne : ¬ K5 = (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))).length := by omega
    have g45 := getElem!_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))) (decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) (pre ++ 43#u8 :: build) 45#u8 K5 (by simp) hpL.symm
    have iP := identM_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ [45#u8]) pre (43#u8 :: build) true (K5 + 1)
      (by simp) (by simp at hpL ⊢; omega) (stopper_plus _) hpre
    have sP := sub_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ [45#u8]) pre (43#u8 :: build) (K5 + 1) (by simp) (by simp at hpL ⊢; omega)
    have hne2 : ¬ K5 + 1 + pre.length = K5 + 1 := by omega
    have hlt : K5 + 1 + pre.length < (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))).length := by omega
    have g43 := getElem!_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ 45#u8 :: pre) build 43#u8 (K5 + 1 + pre.length) (by simp)
      (by simp at hpL ⊢; omega)
    have iB := identM_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ 45#u8 :: pre ++ [43#u8]) build [] false (K5 + 1 + pre.length + 1)
      (by simp) (by simp at hpL ⊢; omega) stopper_nil hbuild
    have sB := sub_at (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))) ((decimal M ++ DOT :: (decimal m ++ DOT :: decimal p)) ++ 45#u8 :: pre ++ [43#u8]) build [] (K5 + 1 + pre.length + 1)
      (by simp) (by simp at hpL ⊢; omega)
    have hne3 : ¬ K5 + 1 + pre.length + 1 + build.length = K5 + 1 + pre.length + 1 := by omega
    have hfin : ¬ K5 + 1 + pre.length + 1 + build.length < (decimal M ++ DOT :: (decimal m ++ DOT :: (decimal p ++ 45#u8 :: (pre ++ 43#u8 :: build)))).length := by omega
    unfold parseM
    simp only [hne, ite_false, f1, f2, f3, f4, f5, hK5ne, g45, ite_true, iP, hne2, sP, hlt, g43, and_self,
      iB, hne3, sB, hfin]

end SemverProofs
