/-
  Pure reference specification of percent-encoding.

  This file does not depend on the Aeneas translation (except for the
  `AsciiSet` type, which we read through its bit mask). Everything here is
  ordinary functional Lean that a reader can check by eye.
-/
module
public import PercentEncoding
@[expose] public section

open Aeneas Aeneas.Std

namespace percent_encoding.Spec

/-- Byte `b` is a member of the set: ASCII and its bit is set in the mask. -/
def inSet (s : ascii_set.AsciiSet) (b : Nat) : Bool :=
  b < 128 && (s.mask.val[b / 32]!).val.testBit (b % 32)

/-- Mirrors `AsciiSet::should_percent_encode`: non-ASCII bytes are always
    encoded, ASCII bytes are encoded when they are in the set. -/
def shouldEncode (s : ascii_set.AsciiSet) (b : Nat) : Bool :=
  !(b < 128) || inSet s b

/-- Upper-case hex digit for `n < 16`, as an ASCII code. -/
def hexDigit (n : Nat) : Nat := if n < 10 then 48 + n else 55 + n

/-- `%XY` for a byte (upper-case hex), as ASCII codes. -/
def encByte (b : Nat) : List Nat := [37, hexDigit (b / 16), hexDigit (b % 16)]

/-- Reference encoder over byte values. -/
def encode (s : ascii_set.AsciiSet) : List Nat → List Nat
  | [] => []
  | b :: rest => (if shouldEncode s b then encByte b else [b]) ++ encode s rest

/-- Value of an ASCII hex digit (either case), if it is one. -/
def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

/-- Reference decoder: `%` followed by two hex digits becomes one byte;
    anything else (including a lone or malformed `%`) is copied unchanged. -/
def decode : List Nat → List Nat
  | [] => []
  | 37 :: h :: l :: rest =>
    match hexVal h, hexVal l with
    | some hv, some lv => (16 * hv + lv) :: decode rest
    | _, _ => 37 :: decode (h :: l :: rest)
  | b :: rest => b :: decode rest
termination_by l => l.length

/-- The byte encoded by the two characters after a `%`, if they are hex digits. -/
def afterPct : List Nat → Option Nat
  | h :: l :: _ =>
    match hexVal h, hexVal l with
    | some hv, some lv => some (16 * hv + lv)
    | _, _ => none
  | _ => none

/-- Byte values of a byte slice. -/
def bytes (s : Slice U8) : List Nat := s.val.map (·.val)

/-- Byte values of a string slice (`Str` is a byte slice in Aeneas). -/
def strBytes (s : Str) : List Nat := bytes s

end percent_encoding.Spec
