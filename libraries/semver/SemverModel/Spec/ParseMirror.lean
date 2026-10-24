import SemverModel.Code.Types
import SemverModel.Spec.Lists
/-!
# Pure mirrors of the parsing and printing functions
-/
open Aeneas Aeneas.Std
open semver_model

namespace SemverSpec

abbrev Res (α : Type) := core.result.Result α ErrorKind

abbrev U64MAX : Nat := 18446744073709551615

/-- Mirror of the `numeric_identifier` loop. Returns `(value, end)`. -/
def numLoop (s : List U8) (st : Nat) (pos : Position) (len value : Nat) : Res (Nat × Nat) :=
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
    else if st < s.length then .Err (.UnexpectedChar pos) else .Err (.UnexpectedEnd pos)
termination_by s.length - (st + len)

def numM (s : List U8) (st : Nat) (pos : Position) : Res (Nat × Nat) := numLoop s st pos 0 0

def dotM (s : List U8) (st : Nat) (pos : Position) : Res Nat :=
  if h : st < s.length then
    if s[st] = DOT then .Ok (st + 1) else .Err (.UnexpectedCharAfter pos)
  else .Err (.UnexpectedEnd pos)

def isIdentNonDigit (b : U8) : Bool :=
  decide ((65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122) ∨ b = 45#u8)

/-- Mirror of the `identifier` loop. Returns the end index. -/
def identLoop (s : List U8) (st : Nat) (isPre : Bool) (pos : Position) (acc seg : Nat) (nd : Bool) : Res Nat :=
  let k := st + acc + seg
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
    else .Ok (st + acc + seg)
termination_by s.length - (st + acc + seg)

def identM (s : List U8) (st : Nat) (isPre : Bool) : Res Nat :=
  identLoop s st isPre (if isPre then .Pre else .Build) 0 0 false

/-- Mirror of `parse_version`, on the pure version type. -/
def parseM (s : List U8) : Res PVersion :=
  if s.length = 0 then .Err .Empty else
  match numM s 0 .Major with
  | .Err e => .Err e
  | .Ok (major, k) =>
  match dotM s k .Major with
  | .Err e => .Err e
  | .Ok k =>
  match numM s k .Minor with
  | .Err e => .Err e
  | .Ok (minor, k) =>
  match dotM s k .Minor with
  | .Err e => .Err e
  | .Ok k =>
  match numM s k .Patch with
  | .Err e => .Err e
  | .Ok (patch, k) =>
  if k = s.length then .Ok ⟨major, minor, patch, [], []⟩ else
  -- prerelease
  let preRes : Res (List U8 × Nat × Position) :=
    if s[k]! = 45#u8 then
      match identM s (k + 1) true with
      | .Err e => .Err e
      | .Ok e => if e = k + 1 then .Err (.EmptySegment .Pre) else .Ok (sub s (k + 1) e, e, .Pre)
    else .Ok ([], k, .Patch)
  match preRes with
  | .Err e => .Err e
  | .Ok (pre, k, pos) =>
  let buildRes : Res (List U8 × Nat × Position) :=
    if k < s.length ∧ s[k]! = 43#u8 then
      match identM s (k + 1) false with
      | .Err e => .Err e
      | .Ok e => if e = k + 1 then .Err (.EmptySegment .Build) else .Ok (sub s (k + 1) e, e, .Build)
    else .Ok ([], k, pos)
  match buildRes with
  | .Err e => .Err e
  | .Ok (build, k, pos) =>
  if k < s.length then .Err (.UnexpectedCharAfter pos)
  else .Ok ⟨major, minor, patch, pre, build⟩

/-- Decimal digits of `n`, as the model's `push_u64` writes them. -/
def decimal (n : Nat) : List U8 :=
  (if n ≥ 10 then decimal (n / 10) else []) ++ [UScalar.ofNat (48 + n % 10) (by
    have := Nat.mod_lt n (by decide : 10 > 0); scalar_tac)]
termination_by n
decreasing_by omega

/-- Mirror of `version_to_bytes`. -/
def printM (v : PVersion) : List U8 :=
  decimal v.major ++ [DOT] ++ decimal v.minor ++ [DOT] ++ decimal v.patch ++
    (if v.pre.length ≠ 0 then 45#u8 :: v.pre else []) ++
    (if v.build.length ≠ 0 then 43#u8 :: v.build else [])

end SemverSpec
