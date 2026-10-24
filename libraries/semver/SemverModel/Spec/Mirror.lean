import Aeneas
/-!
# Pure mirrors of the extracted functions

Each definition here follows the control flow of one Rust function in
`model/src/lib.rs`, but on `List U8` and `Nat` instead of slices and machine
integers, with no failure. `SemverModel/Proofs/Refine*.lean` proves that the
Aeneas output equals these mirrors. `SemverModel/Proofs/*` then proves the
properties on the mirrors.
-/
open Aeneas Aeneas.Std

namespace SemverSpec

abbrev DOT : U8 := 46#u8

def isDig (b : U8) : Bool := decide (48 ≤ b.val ∧ b.val ≤ 57)

def segEnd (l : List U8) (i : Nat) : Nat :=
  if h : i < l.length then
    if l[i] = DOT then i else segEnd l (i + 1)
  else l.length
termination_by l.length - i

def allDigits (l : List U8) (i e : Nat) : Bool :=
  if i < e then
    if isDig l[i]! then allDigits l (i + 1) e else false
  else true
termination_by e - i

def cmpBytes (s : List U8) (a ae : Nat) (t : List U8) (b be : Nat) : Ordering :=
  if a < ae ∧ b < be then
    if s[a]!.val < t[b]!.val then .lt
    else if s[a]!.val > t[b]!.val then .gt
    else cmpBytes s (a + 1) ae t (b + 1) be
  else if a < ae then .gt
  else if b < be then .lt
  else .eq
termination_by ae - a

theorem cmpBytes_step {s t : List U8} {a ae b be : Nat} (h1 : a < ae) (h2 : b < be)
    (ha : a < s.length) (hb : b < t.length) :
    cmpBytes s a ae t b be =
      if s[a].val < t[b].val then .lt
      else if s[a].val > t[b].val then .gt
      else cmpBytes s (a + 1) ae t (b + 1) be := by
  rw [cmpBytes]; simp [h1, h2, ha, hb, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem]

theorem cmpBytes_stop {s t : List U8} {a ae b be : Nat} (h : ¬ (a < ae ∧ b < be)) :
    cmpBytes s a ae t b be = if a < ae then .gt else if b < be then .lt else .eq := by
  rw [cmpBytes]; simp only [h, if_false]

def cmpNat (a b : Nat) : Ordering :=
  if a < b then .lt else if a > b then .gt else .eq

def skipZeros (l : List U8) (a e : Nat) : Nat :=
  if a < e then
    if l[a]! ≠ 48#u8 then a else skipZeros l (a + 1) e
  else e
termination_by e - a

theorem skipZeros_step {l : List U8} {a e : Nat} (h1 : a < e) (ha : a < l.length) :
    skipZeros l a e = if l[a] ≠ 48#u8 then a else skipZeros l (a + 1) e := by
  rw [skipZeros]; simp [h1, ha, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem]

theorem skipZeros_stop {l : List U8} {a e : Nat} (h1 : ¬ a < e) : skipZeros l a e = e := by
  rw [skipZeros]; simp [h1]

theorem skipZeros_bounds (l : List U8) (a e : Nat) (h : a ≤ e) :
    a ≤ skipZeros l a e ∧ skipZeros l a e ≤ e := by
  fun_induction skipZeros l a e <;> omega

def preSegCmp (l : List U8) (i le : Nat) (r : List U8) (j re : Nat) : Ordering :=
  match allDigits l i le, allDigits r j re with
  | true, true =>
    match cmpNat (le - i) (re - j) with
    | .eq => cmpBytes l i le r j re
    | o => o
  | true, false => .lt
  | false, true => .gt
  | false, false => cmpBytes l i le r j re

def buildSegCmp (l : List U8) (i le : Nat) (r : List U8) (j re : Nat) : Ordering :=
  match allDigits l i le, allDigits r j re with
  | true, true =>
    let li := skipZeros l i le
    let rj := skipZeros r j re
    match cmpNat (le - li) (re - rj) with
    | .eq =>
      match cmpBytes l li le r rj re with
      | .eq => cmpNat (le - i) (re - j)
      | o => o
    | o => o
  | true, false => .lt
  | false, true => .gt
  | false, false => cmpBytes l i le r j re

theorem segEnd_ge (l : List U8) (i : Nat) : i ≤ segEnd l i ∨ l.length < i := by
  fun_induction segEnd l i <;> omega

theorem segEnd_le (l : List U8) (i : Nat) : segEnd l i ≤ l.length ∨ l.length < i := by
  fun_induction segEnd l i <;> omega

theorem segEnd_ge' (l : List U8) (i : Nat) (h : i ≤ l.length) : i ≤ segEnd l i := by
  have := segEnd_ge l i; omega

def cmpSegsLoop (l r : List U8) (build : Bool) (i j : Nat) (rdone : Bool) : Ordering :=
  if hi : i ≤ l.length then
    let le := segEnd l i
    if rdone then .gt
    else
      let re := segEnd r j
      let o := if build then buildSegCmp l i le r j re else preSegCmp l i le r j re
      match o with
      | .eq =>
        let jr : Nat × Bool := if re = r.length then (j, true) else (re + 1, rdone)
        if le = l.length then (if jr.2 then .eq else .lt)
        else cmpSegsLoop l r build (le + 1) jr.1 jr.2
      | o => o
  else .eq
termination_by l.length + 1 - i
decreasing_by have := segEnd_ge' l i hi; omega

theorem cmpSegsLoop_unfold (l r : List U8) (build : Bool) (i j : Nat) (rdone : Bool) (hi : i ≤ l.length) :
    cmpSegsLoop l r build i j rdone =
      (let le := segEnd l i
      if rdone then .gt
      else
        let re := segEnd r j
        let o := if build then buildSegCmp l i le r j re else preSegCmp l i le r j re
        match o with
        | .eq =>
          let jr : Nat × Bool := if re = r.length then (j, true) else (re + 1, rdone)
          if le = l.length then (if jr.2 then .eq else .lt)
          else cmpSegsLoop l r build (le + 1) jr.1 jr.2
        | o => o) := by
  rw [cmpSegsLoop]; simp only [hi, _root_.dite_true]

theorem segEnd_bounds (l : List U8) (i : Nat) (h : i ≤ l.length) : i ≤ segEnd l i ∧ segEnd l i ≤ l.length := by
  have := segEnd_ge l i; have := segEnd_le l i; omega

def preCmp (l r : List U8) : Ordering :=
  if l.length = 0 then
    if r.length = 0 then .eq else .gt
  else if r.length = 0 then .lt
  else cmpSegsLoop l r false 0 0 false

def buildCmp (l r : List U8) : Ordering :=
  if l.length = 0 ∧ r.length = 0 then .eq
  else cmpSegsLoop l r true 0 0 false

/-- Pure view of a `Version`: the three numbers and the two byte strings. -/
structure PVersion where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List U8
  build : List U8
deriving DecidableEq

def versionCmp (a b : PVersion) : Ordering :=
  match cmpNat a.major b.major with
  | .eq =>
    match cmpNat a.minor b.minor with
    | .eq =>
      match cmpNat a.patch b.patch with
      | .eq =>
        match preCmp a.pre b.pre with
        | .eq => buildCmp a.build b.build
        | o => o
      | o => o
    | o => o
  | o => o

end SemverSpec
