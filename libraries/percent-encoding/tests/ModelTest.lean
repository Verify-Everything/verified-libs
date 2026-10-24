/-
  Differential test of the hand-written std models (PercentEncoding/FunsExternal.lean)
  against real Rust std. Vectors come from rust/modeltest (`kind|input|expected`).
  Run: lake env lean --run tests/ModelTest.lean <vectors.txt>
-/
import PercentEncoding
open Aeneas Aeneas.Std Result percent_encoding

def u8 (n : Nat) : Std.U8 := ⟨BitVec.ofNat 8 n⟩
def u32 (n : Nat) : Std.U32 := ⟨BitVec.ofNat 32 n⟩

def sl (l : List Nat) : Slice Std.U8 :=
  if h : (l.map u8).length ≤ Usize.max then Slice.from (l.map u8) h else Slice.from [] (by simp)

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48 else c.toNat - 87

def unhex (s : String) : List Nat :=
  let rec go : List Char → List Nat
    | a :: b :: r => (hexVal a * 16 + hexVal b) :: go r
    | _ => []
  go s.toList

def hexNat (s : String) : Nat := s.toList.foldl (fun acc c => acc * 16 + hexVal c) 0

def toHex (l : List Nat) : String :=
  String.join (l.map fun n =>
    let d := fun k => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])

def bytesOf (s : Slice Std.U8) : List Nat := s.val.map (·.val)
def strBytesOf (s : String) : List Nat := (stringBytes s).map (·.val)

def resStr {α} (r : Result α) (f : α → String) : String :=
  match r.match with
  | .ok a => f a
  | .vis _ _ => "P"
  | .div => "D"

/-- The model's answer, in the same format the Rust side prints. -/
def model (kind input : String) : Option String :=
  match kind with
  | "char_from_u8" =>
    some (resStr (Char.Insts.CoreConvertFromU8.from (u8 (hexNat input))) fun c => toHexNat c.toNat)
  | "is_ascii" =>
    some (resStr (core.num.U8.is_ascii (u8 (hexNat input))) fun b => if b then "1" else "0")
  | "to_digit" =>
    match input.splitOn "," with
    | [c, r] =>
      let ch := Char.ofNat (hexNat c)
      some (resStr (core.char.methods.Char.to_digit ch (u32 (hexNat r)))
        fun o => match o with | none => "N" | some d => toHexNat d.val)
    | _ => none
  | "utf8" =>
    let s := sl (unhex input)
    let v := resStr (core.str.converts.from_utf8 s) fun r =>
      match r with | .Ok _ => "V" | .Err _ => "I"
    let v2 := resStr (alloc.string.String.from_utf8 ⟨s⟩) fun r =>
      match r with | .Ok st => if strBytesOf st = unhex input then "V" else "X" | .Err _ => "I"
    let l := resStr (alloc.string.String.from_utf8_lossy s) fun c =>
      match c with
      | .Borrowed b => "B" ++ toHex (bytesOf b)
      | .Owned o => "O" ++ toHex (strBytesOf o)
    if v = v2 then some (v ++ l) else some ("MISMATCH core/String " ++ v ++ v2)
  | "strops" =>
    match input.splitOn "," with
    | [a, b, c] =>
      some (resStr (do
        let s ← Str.Insts.AllocBorrowToOwnedString.to_owned (sl (unhex a))
        let s ← alloc.string.String.push_str s (sl (unhex b))
        let s ← alloc.string.String.push_str s (sl (unhex c))
        alloc.string.String.push_str s (sl (unhex b))) fun s => toHex (strBytesOf s))
    | _ => none
  | "slice" =>
    match input.splitOn "," with
    | [v, k] =>
      let s := sl (unhex v)
      let k := hexNatDec k
      let it : core.slice.iter.Iter Std.U8 := ⟨s, k⟩
      some (resStr (do
        let sf ← core.slice.Slice.split_first s
        let it2 ← core.slice.iter.Iter.Insts.CoreCloneClone.clone it
        let n ← core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT.len it2
        let rest ← core.slice.iter.Iter.as_slice it2
        let w ← Slice.Insts.AllocBorrowToOwnedVec.to_owned core.clone.CloneU8 (sl ((unhex v).take k))
        let wb ← alloc.vec.Vec.Insts.CoreBorrowBorrowSlice.borrow (Slice Std.U8) w
        pure (sf, n, rest, wb)) fun ⟨sf, n, rest, wb⟩ =>
          let sfs := match sf with
            | none => "N"
            | some (x, r) => toHex [x.val] ++ "," ++ toHex (bytesOf r)
          sfs ++ ";" ++ toString n.val ++ ";" ++ toHex (bytesOf rest) ++ ";" ++
            toHex (bytesOf wb ++ (unhex v).drop k))
    | _ => none
  | _ => none
where
  toHexNat (n : Nat) : String := String.ofList (Nat.toDigits 16 n)
  hexNatDec (s : String) : Nat := s.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

def main (args : List String) : IO UInt32 := do
  let path := args.headD "vectors.txt"
  let lines ← IO.FS.lines path
  let mut fails := 0
  let mut counts : Std.HashMap String Nat := {}
  for line in lines do
    match line.splitOn "|" with
    | [kind, input, expected] =>
      counts := counts.insert kind (counts.getD kind 0 + 1)
      match model kind input with
      | some got =>
        if got != expected then
          fails := fails + 1
          if fails ≤ 20 then IO.println s!"FAIL {kind} {input}: model {got}, Rust {expected}"
      | none =>
        fails := fails + 1
        IO.println s!"UNKNOWN {line}"
    | _ => pure ()
  for (k, n) in counts.toList do IO.println s!"{k}: {n} vectors"
  IO.println s!"failures: {fails}"
  return (if fails = 0 then 0 else 1)
