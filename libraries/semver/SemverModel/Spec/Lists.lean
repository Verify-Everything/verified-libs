import SemverModel.Spec.Mirror
/-!
# From index-based mirrors to list-based specifications

The mirrors walk index ranges. Here we show they compute clean functions of
the sub-lists those ranges denote.
-/
open Aeneas Aeneas.Std

namespace SemverSpec

/-- The sub-list `l[a..e]`. -/
def sub (l : List U8) (a e : Nat) : List U8 := (l.take e).drop a

theorem sub_cons {l : List U8} {a e : Nat} (h1 : a < e) (h2 : e ≤ l.length) :
    sub l a e = l[a] :: sub l (a + 1) e := by
  unfold sub
  have : a < (l.take e).length := by simp; omega
  rw [List.drop_eq_getElem_cons this]
  simp

theorem sub_nil {l : List U8} {a e : Nat} (h : e ≤ a) : sub l a e = [] := by
  unfold sub; simp; omega

theorem sub_length (l : List U8) (a e : Nat) (h : e ≤ l.length) : (sub l a e).length = e - a := by
  unfold sub; simp; omega

/-- Byte comparison on the numeric value. -/
def byteCmp (x y : U8) : Ordering := compare x.val y.val

theorem allDigits_eq (l : List U8) (i e : Nat) (h : e ≤ l.length) :
    allDigits l i e = (sub l i e).all isDig := by
  fun_induction allDigits l i e with
  | case1 i hi hd ih =>
    rw [sub_cons hi h]; simp only [List.all_cons]
    rw [← ih]; simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < l.length)] at hd
    simp [hd]
  | case2 i hi hd =>
    rw [sub_cons hi h]; simp only [List.all_cons]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < l.length)] at hd
    simp [hd]
  | case3 i hi =>
    rw [sub_nil (by omega)]; rfl

theorem cmpBytes_eq (s t : List U8) (a ae b be : Nat) (hs : ae ≤ s.length) (ht : be ≤ t.length) :
    cmpBytes s a ae t b be = List.compareLex byteCmp (sub s a ae) (sub t b be) := by
  fun_induction cmpBytes s a ae t b be with
  | case1 a b hab hlt =>
    rw [sub_cons hab.1 hs, sub_cons hab.2 ht, List.compareLex_cons_cons]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : a < s.length),
      List.getElem?_eq_getElem (by omega : b < t.length)] at hlt
    simp [byteCmp, compare, compareOfLessAndEq, hlt]
  | case2 a b hab hlt hgt =>
    rw [sub_cons hab.1 hs, sub_cons hab.2 ht, List.compareLex_cons_cons]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : a < s.length),
      List.getElem?_eq_getElem (by omega : b < t.length)] at hlt hgt
    have : ¬ s[a].val = t[b].val := by omega
    have h' : ¬ s[a].val < t[b].val := by omega
    simp [byteCmp, compare, compareOfLessAndEq, h', this]
  | case3 a b hab hlt hgt ih =>
    rw [sub_cons hab.1 hs, sub_cons hab.2 ht, List.compareLex_cons_cons, ← ih]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : a < s.length),
      List.getElem?_eq_getElem (by omega : b < t.length)] at hlt hgt
    have : s[a].val = t[b].val := by omega
    simp [byteCmp, compare, compareOfLessAndEq, this]
  | case4 a b hab ha =>
    have hb : ¬ b < be := by omega
    rw [sub_cons ha hs, sub_nil (l := t) (by omega)]; rfl
  | case5 a b hab ha hb =>
    rw [sub_nil (l := s) (by omega), sub_cons hb ht]; rfl
  | case6 a b hab ha hb =>
    rw [sub_nil (l := s) (by omega), sub_nil (l := t) (by omega)]; rfl

end SemverSpec

namespace SemverSpec

def bytesN (x : List U8) : List Nat := x.map (·.val)

theorem compareLex_byteCmp (x y : List U8) :
    List.compareLex byteCmp x y = compare (bytesN x) (bytesN y) := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a x ih =>
    cases y with
    | nil => rfl
    | cons b y =>
      simp only [bytesN, List.map_cons, List.compareLex_cons_cons, List.compare_cons_cons] at *
      rw [ih]; rfl

theorem bytesN_inj {x y : List U8} (h : bytesN x = bytesN y) : x = y := by
  unfold bytesN at h
  apply List.map_injective_iff.mpr _ h
  intro a b hab; exact UScalar.eq_of_val_eq hab

def isZero (b : U8) : Bool := decide (b = 48#u8)
def trim (x : List U8) : List U8 := x.dropWhile isZero

theorem skipZeros_eq (l : List U8) (a e : Nat) (h : e ≤ l.length) :
    sub l (skipZeros l a e) e = trim (sub l a e) := by
  fun_induction skipZeros l a e with
  | case1 a ha hz =>
    rw [sub_cons ha h, trim, List.dropWhile_cons]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : a < l.length)] at hz
    simp [isZero, hz, ← sub_cons ha h]
  | case2 a ha hz ih =>
    rw [ih, sub_cons ha h (l := l), trim, trim, List.dropWhile_cons]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : a < l.length)] at hz
    simp [isZero, hz]
  | case3 a ha =>
    rw [sub_nil (le_refl e), sub_nil (by omega)]; rfl

def isNum (x : List U8) : Bool := x.all isDig

/-- Prerelease segment order, as a key comparison:
numeric segments first (by length, then bytes), then the rest (by bytes). -/
def preSegL : List U8 → List U8 → Ordering :=
  compareLex (compareOn fun x => if isNum x then 0 else 1)
    (compareLex (compareOn fun x => if isNum x then x.length else 0) (compareOn bytesN))

/-- Build-metadata segment order, as a key comparison. Numeric segments compare by
value (length then bytes without leading zeros), then by total length. -/
def buildSegL : List U8 → List U8 → Ordering :=
  compareLex (compareOn fun x => if isNum x then 0 else 1)
    (compareLex (compareOn fun x => if isNum x then (trim x).length else 0)
      (compareLex (compareOn fun x => if isNum x then bytesN (trim x) else [])
        (compareLex (compareOn fun x => if isNum x then x.length else 0) (compareOn bytesN))))

theorem cmpNat_eq (a b : Nat) : cmpNat a b = compare a b := by
  unfold cmpNat; simp only [compare, compareOfLessAndEq]
  split_ifs <;> first | rfl | omega

theorem preSegCmp_eq (l : List U8) (i le : Nat) (r : List U8) (j re : Nat)
    (h1 : le ≤ l.length) (h2 : re ≤ r.length) :
    preSegCmp l i le r j re = preSegL (sub l i le) (sub r j re) := by
  unfold preSegCmp preSegL
  rw [allDigits_eq _ _ _ h1, allDigits_eq _ _ _ h2, cmpBytes_eq _ _ _ _ _ _ h1 h2, compareLex_byteCmp]
  have e1 := sub_length l i le h1
  have e2 := sub_length r j re h2
  simp only [compareLex, compareOn, isNum]
  rw [e1, e2, cmpNat_eq]
  by_cases hx : (sub l i le).all isDig = true <;> by_cases hy : (sub r j re).all isDig = true <;>
    simp only [hx, hy, Bool.false_eq_true, ite_true, ite_false] <;> try rfl

theorem trim_decomp (x : List U8) :
    x = List.replicate (x.length - (trim x).length) 48#u8 ++ trim x := by
  have h := List.takeWhile_append_dropWhile (p := isZero) (l := x)
  have hrep : x.takeWhile isZero = List.replicate (x.takeWhile isZero).length 48#u8 := by
    rw [List.eq_replicate_iff]; refine ⟨rfl, ?_⟩
    intro b hb
    have := List.all_takeWhile (p := isZero) (l := x)
    rw [List.all_eq_true] at this
    simpa [isZero] using this b hb
  have hl : x.length = (x.takeWhile isZero).length + (trim x).length := by
    conv => lhs; rw [← h]
    simp only [List.length_append, trim]
  unfold trim at *
  conv => lhs; rw [← h]
  rw [hrep]; simp; omega

theorem eq_of_trim_eq {x y : List U8} (h1 : trim x = trim y) (h2 : x.length = y.length) : x = y := by
  rw [trim_decomp x, trim_decomp y, h1, h2]

theorem buildSegCmp_eq (l : List U8) (i le : Nat) (r : List U8) (j re : Nat)
    (h0 : i ≤ le) (h1 : le ≤ l.length) (h0' : j ≤ re) (h2 : re ≤ r.length) :
    buildSegCmp l i le r j re = buildSegL (sub l i le) (sub r j re) := by
  unfold buildSegCmp buildSegL
  dsimp only
  have b1 := skipZeros_bounds l i le h0
  have b2 := skipZeros_bounds r j re h0'
  rw [allDigits_eq _ _ _ h1, allDigits_eq _ _ _ h2, cmpBytes_eq _ _ _ _ _ _ h1 h2, compareLex_byteCmp,
    cmpBytes_eq _ _ _ _ _ _ h1 h2, compareLex_byteCmp, skipZeros_eq _ _ _ h1, skipZeros_eq _ _ _ h2]
  have e1 := sub_length l i le h1
  have e2 := sub_length r j re h2
  have t1 : (trim (sub l i le)).length = le - skipZeros l i le := by
    rw [← skipZeros_eq _ _ _ h1, sub_length _ _ _ h1]
  have t2 : (trim (sub r j re)).length = re - skipZeros r j re := by
    rw [← skipZeros_eq _ _ _ h2, sub_length _ _ _ h2]
  simp only [compareLex, compareOn, isNum]
  rw [e1, e2, t1, t2, cmpNat_eq, cmpNat_eq]
  by_cases hx : (sub l i le).all isDig = true <;> by_cases hy : (sub r j re).all isDig = true <;>
    simp only [hx, hy, Bool.false_eq_true, ite_true, ite_false] <;> try rfl
  -- both numeric
  cases hc1 : compare (le - skipZeros l i le) (re - skipZeros r j re) <;> try rfl
  cases hc2 : compare (bytesN (trim (sub l i le))) (bytesN (trim (sub r j re))) <;> try rfl
  have ht : trim (sub l i le) = trim (sub r j re) := bytesN_inj (by simpa using hc2)
  cases hc3 : compare (le - i) (re - j) <;> try rfl
  have hl : le - i = re - j := by simpa using hc3
  have := eq_of_trim_eq ht (by rw [e1, e2, hl])
  simp [this]

theorem segEnd_dot (l : List U8) (i : Nat) (h : segEnd l i < l.length) :
    l[segEnd l i] = DOT := by
  fun_induction segEnd l i with
  | case1 i hi hd => simpa using hd
  | case2 i hi hd ih => exact ih h
  | case3 i hi => omega

theorem segEnd_nodot (l : List U8) (i : Nat) (k : Nat) (hik : i ≤ k) (hk : k < segEnd l i) (hl : k < l.length) :
    l[k] ≠ DOT := by
  fun_induction segEnd l i with
  | case1 i hi hd => omega
  | case2 i hi hd ih =>
    by_cases hki : k = i
    · subst hki; exact hd
    · exact ih (by omega) hk
  | case3 i hi =>
    intro h; omega

/-- `str::split('.')` on `l[i..]`. -/
def splitFrom (l : List U8) (i : Nat) : List (List U8) :=
  if h : i ≤ l.length then
    let e := segEnd l i
    sub l i e :: (if e = l.length then [] else splitFrom l (e + 1))
  else []
termination_by l.length + 1 - i
decreasing_by have := segEnd_ge' l i h; omega

def splitDot (l : List U8) : List (List U8) := splitFrom l 0

theorem splitFrom_unfold (l : List U8) (i : Nat) (h : i ≤ l.length) :
    splitFrom l i = sub l i (segEnd l i) ::
      (if segEnd l i = l.length then [] else splitFrom l (segEnd l i + 1)) := by
  rw [splitFrom]; simp only [h, _root_.dite_true]

theorem splitFrom_ne_nil (l : List U8) (i : Nat) (h : i ≤ l.length) : splitFrom l i ≠ [] := by
  rw [splitFrom_unfold l i h]; simp

theorem sub_full (l : List U8) (i : Nat) : sub l i l.length = l.drop i := by
  simp [sub]

theorem drop_split (l : List U8) (i e : Nat) (h1 : i ≤ e) (h2 : e < l.length) :
    l.drop i = sub l i e ++ l[e] :: l.drop (e + 1) := by
  unfold sub
  rw [← List.drop_eq_getElem_cons h2]
  have : l.drop i = (l.take e).drop i ++ l.drop e := by
    rw [← List.drop_append_of_le_length (by simp; omega), List.take_append_drop]
  exact this

theorem intercalate_splitFrom (l : List U8) (i : Nat) (h : i ≤ l.length) :
    [DOT].intercalate (splitFrom l i) = l.drop i := by
  fun_induction splitFrom l i with
  | case1 i hi e ih =>
    have b := segEnd_bounds l i hi
    by_cases he : segEnd l i = l.length
    · simp only [e, he, ite_true, List.intercalate_singleton, sub_full]
    · simp only [e, he, ite_false] at ih ⊢
      have hlt : segEnd l i < l.length := by omega
      rw [List.intercalate_cons_of_ne_nil (splitFrom_ne_nil l _ (by omega)), ih (by omega),
        drop_split l i (segEnd l i) b.1 hlt, segEnd_dot l i hlt]
      simp
  | case2 i hi => omega

theorem splitDot_inj {l r : List U8} (h : splitDot l = splitDot r) : l = r := by
  have h1 := intercalate_splitFrom l 0 (Nat.zero_le _)
  have h2 := intercalate_splitFrom r 0 (Nat.zero_le _)
  unfold splitDot at h
  rw [h] at h1; rw [h1] at h2; simpa using h2

def segL (build : Bool) : List U8 → List U8 → Ordering := if build then buildSegL else preSegL

theorem cmpSegsLoop_eq (l r : List U8) (b : Bool) (i j : Nat) (rd : Bool)
    (hi : i ≤ l.length) (hj : j ≤ r.length) :
    cmpSegsLoop l r b i j rd =
      List.compareLex (segL b) (splitFrom l i) (if rd then [] else splitFrom r j) := by
  induction hn : l.length + 1 - i using Nat.strong_induction_on generalizing i j rd with
  | _ n ih =>
  rw [cmpSegsLoop_unfold _ _ _ _ _ _ hi, splitFrom_unfold l i hi]
  have bl := segEnd_bounds l i hi
  have br := segEnd_bounds r j hj
  cases rd
  · simp only [Bool.false_eq_true, ite_false]
    rw [splitFrom_unfold r j hj, List.compareLex_cons_cons]
    have hseg : (if b then buildSegCmp l i (segEnd l i) r j (segEnd r j)
        else preSegCmp l i (segEnd l i) r j (segEnd r j)) = segL b (sub l i (segEnd l i)) (sub r j (segEnd r j)) := by
      cases b
      · simp [segL, preSegCmp_eq _ _ _ _ _ _ bl.2 br.2]
      · simp [segL, buildSegCmp_eq _ _ _ _ _ _ bl.1 bl.2 br.1 br.2]
    simp only [hseg]
    cases segL b (sub l i (segEnd l i)) (sub r j (segEnd r j))
    · rfl
    · simp only [Ordering.then]
      by_cases hle : segEnd l i = l.length <;> by_cases hre : segEnd r j = r.length
      · simp [hle, hre]; rfl
      · simp only [hle, hre, ite_true, ite_false]
        rw [splitFrom_unfold r _ (by omega)]; rfl
      · simp only [hle, hre, ite_true, ite_false]
        rw [ih _ (by omega) _ _ _ (by omega) hj rfl]
        simp only [ite_true]
      · simp only [hle, hre, ite_true, ite_false]
        rw [ih _ (by omega) _ _ _ (by omega) (by omega) rfl]
        simp only [Bool.false_eq_true, ite_false]
    · rfl
  · simp only [ite_true]; rfl
