import SemverModel.Proofs.RefineCmp
import SemverModel.Spec.ParseMirror
/-! Refinement: the Aeneas-generated parsing and printing functions equal the pure mirrors. -/
open Aeneas Aeneas.Std Result ControlFlow
open semver_model SemverSpec

namespace SemverProofs

def resMap {α β : Type} (f : α → β) : core.result.Result α ErrorKind → core.result.Result β ErrorKind
  | .Ok a => .Ok (f a)
  | .Err e => .Err e

@[simp] theorem resMap_ok {α β : Type} (f : α → β) (a : α) : resMap f (.Ok a) = .Ok (f a) := rfl
@[simp] theorem resMap_err {α β : Type} (f : α → β) (e : ErrorKind) : resMap f (.Err e) = (.Err e : core.result.Result β ErrorKind) := rfl

theorem numLoop_unfold (s : List U8) (st : Nat) (pos : Position) (len value : Nat) :
    numLoop s st pos len value =
    if h : st + len < s.length then
      let d := s[st + len]
      if d.val < 48 ∨ d.val > 57 then
        if len > 0 then .Ok (value, st + len)
        else if st < s.length then .Err (.UnexpectedChar pos) else .Err (.UnexpectedEnd pos)
      else if value = 0 ∧ len > 0 then .Err (.LeadingZero pos)
      else if value * 10 > U64MAX then .Err (.Overflow pos)
      else if value * 10 + (d.val - 48) > U64MAX then .Err (.Overflow pos)
      else numLoop s st pos (len + 1) (value * 10 + (d.val - 48))
    else
      if len > 0 then .Ok (value, st + len)
      else if st < s.length then .Err (.UnexpectedChar pos) else .Err (.UnexpectedEnd pos) := by
  rw [numLoop]

@[step]
theorem numeric_identifier_loop_spec (s : Slice U8) (st : Usize) (pos : Position) (len : Usize) (value : U64)
    (h : st.val + len.val ≤ s.length) :
    numeric_identifier_loop s st pos len value ⦃ r =>
      resMap (fun p => (p.1.val, p.2.val)) r = numLoop s.val st.val pos len.val value.val ⦄ := by
  unfold numeric_identifier_loop
  apply loop.spec_decr_nat (fun x => s.length - (st.val + x.1.val))
    (fun x => st.val + x.1.val ≤ s.length ∧
      numLoop s.val st.val pos x.1.val x.2.val = numLoop s.val st.val pos len.val value.val)
  · intro ⟨l, v⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hsl : s.length = s.val.length := rfl
    unfold numeric_identifier_loop.body
    step*
    all_goals (rw [← h2]; clear h2; rw [numLoop_unfold s.val st.val pos l.val v.val]
               by_cases hk : st.val + l.val < s.val.length <;>
               simp only [UScalar.lt_equiv, gt_iff_lt] at * <;> simp_all [U64MAX, U64.max_eq] <;> (try split_ifs) <;> (try omega) <;> (try scalar_tac))
  · exact ⟨h, rfl⟩

theorem numeric_identifier_spec (s : Slice U8) (st : Usize) (pos : Position) (h : st.val ≤ s.length) :
    numeric_identifier s st pos ⦃ r => resMap (fun p => (p.1.val, p.2.val)) r = numM s.val st.val pos ⦄ := by
  unfold numeric_identifier numM
  step*

theorem dot_spec (s : Slice U8) (st : Usize) (pos : Position) :
    dot s st pos ⦃ r => resMap (fun e => e.val) r = dotM s.val st.val pos ⦄ := by
  unfold dot dotM
  step*
  all_goals (have hsl : s.length = s.val.length := rfl
             by_cases hk : st.val < s.val.length <;> simp_all <;> scalar_tac)

@[step]
theorem is_ident_char_nondigit_spec (b : U8) : is_ident_char_nondigit b ⦃ r => r = isIdentNonDigit b ⦄ := by
  unfold is_ident_char_nondigit isIdentNonDigit
  have h45 : b = 45#u8 ↔ b.val = 45 := by rw [UScalar.eq_equiv]; simp
  split_ifs <;> simp only [WP.spec_ok, h45, UScalar.le_equiv, ge_iff_le] at * <;>
    simp only [decide_eq_decide, Bool.true_eq, decide_eq_true_eq] <;> scalar_tac

theorem identLoop_unfold (s : List U8) (st : Nat) (isPre : Bool) (pos : Position) (acc seg : Nat) (nd : Bool) :
    identLoop s st isPre pos acc seg nd =
    (let k := st + acc + seg
    if hk : k < s.length then
      let c := s[k]
      if isIdentNonDigit c then identLoop s st isPre pos acc (seg + 1) true
      else if isDig c then identLoop s st isPre pos acc (seg + 1) nd
      else if seg = 0 then
        if acc = 0 then (if c = DOT then .Err (.EmptySegment pos) else .Ok st)
        else .Err (.EmptySegment pos)
      else if isPre ∧ seg > 1 ∧ nd = false ∧ s[st + acc]! = 48#u8 then .Err (.LeadingZero pos)
      else if c = DOT then identLoop s st isPre pos (acc + seg + 1) 0 false
      else .Ok (st + acc + seg)
    else
      if seg = 0 then
        if acc = 0 then .Ok st else .Err (.EmptySegment pos)
      else if isPre ∧ seg > 1 ∧ nd = false ∧ s[st + acc]! = 48#u8 then .Err (.LeadingZero pos)
      else .Ok (st + acc + seg)) := by
  rw [identLoop]

@[simp] theorem isIdentNonDigit_zero : isIdentNonDigit 0#u8 = false := by
  unfold isIdentNonDigit; decide

@[simp] theorem isDig_zero : isDig 0#u8 = false := by
  unfold isDig; decide

set_option hygiene false in
macro "ident_close" : tactic => `(tactic|
  first
  | (exfalso; simp only [isIdentNonDigit_zero, isDig_zero] at *; subst_vars; contradiction)
  | (rw [← h2]; clear h2; rw [identLoop_unfold s.val st.val _ pos a.val g.val n]
     (try have hacc : st.val + a.val < s.val.length := by scalar_tac)
     by_cases hk : st.val + a.val + g.val < s.val.length <;>
     simp only [UScalar.lt_equiv, gt_iff_lt] at * <;> simp_all [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem] <;>
     (try split_ifs) <;> (try omega) <;> (try scalar_tac) <;> (try simp only [Nat.add_assoc]) <;> (try (congr 1; omega))))

set_option maxHeartbeats 2000000 in
@[step]
theorem identifier_loop_spec (s : Slice U8) (st : Usize) (isPre : Bool) (pos : Position) (acc seg : Usize) (nd : Bool)
    (h : st.val + acc.val + seg.val ≤ s.length) :
    identifier_loop s st isPre pos acc seg nd ⦃ r =>
      resMap (fun e => e.val) r = identLoop s.val st.val isPre pos acc.val seg.val nd ⦄ := by
  unfold identifier_loop
  apply loop.spec_decr_nat (fun x => s.length - (st.val + x.1.val + x.2.1.val))
    (fun x => st.val + x.1.val + x.2.1.val ≤ s.length ∧
      identLoop s.val st.val isPre pos x.1.val x.2.1.val x.2.2 = identLoop s.val st.val isPre pos acc.val seg.val nd)
  · intro ⟨a, g, n⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hsl : s.length = s.val.length := rfl
    unfold identifier_loop.body
    cases isPre
    · step*
      split
      · step*
        all_goals ident_close
      · step*
        all_goals ident_close
    · step*
      split
      · step*
        all_goals ident_close
      · step*
        all_goals ident_close
  · exact ⟨h, rfl⟩

end SemverProofs
