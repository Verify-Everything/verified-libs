/-
  Cross-check of the Aeneas translation: evaluates the extracted Lean code (PercentEncoding/Funs.lean)
  on vectors produced by the compiled, unpatched upstream crate (rust/crosscheck).
  Run: lake env lean --run tests/CrossCheck.lean <cross.txt>
-/
import PercentEncoding
open Aeneas Aeneas.Std Result percent_encoding

def u8 (n : Nat) : Std.U8 := ⟨BitVec.ofNat 8 n⟩
def sl (l : List Nat) : Slice Std.U8 :=
  if h : (l.map u8).length ≤ Usize.max then Slice.from (l.map u8) h else Slice.from [] (by simp)

def hexVal (c : Char) : Nat := if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48 else c.toNat - 87
def unhex (s : String) : List Nat :=
  let rec go : List Char → List Nat
    | a :: b :: r => (hexVal a * 16 + hexVal b) :: go r
    | _ => []
  go s.toList
def toHex (l : List Nat) : String :=
  String.join (l.map fun n =>
    let d := fun k => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])
def dec (s : String) : Nat := s.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

def bytesOf (s : Slice Std.U8) : List Nat := s.val.map (·.val)
def strBytesOf (s : String) : List Nat := (stringBytes s).map (·.val)
def cowStr : alloc.borrow.Cow Str String → String
  | .Borrowed s => "B" ++ toHex (bytesOf s)
  | .Owned s => "O" ++ toHex (strBytesOf s)

def show? {α} (r : Result α) (f : α → String) : String :=
  match r.match with
  | .ok a => f a
  | .vis _ _ => "P"
  | .div => "D"

def mkSets : Result (List ascii_set.AsciiSet) := do
  let c ← ascii_set.CONTROLS
  let na ← ascii_set.NON_ALPHANUMERIC
  let c0 ← c.add (u8 0)
  let na0 ← na.add (u8 0)
  let s2 ← do
    let s ← c.add (u8 32); let s ← s.add (u8 34); let s ← s.add (u8 35)
    let s ← s.add (u8 60); s.add (u8 62)
  let s3 ← do
    let s ← na.remove (u8 45); let s ← s.remove (u8 46); let s ← s.remove (u8 95)
    s.remove (u8 126)
  let s4 ← c.complement
  let s5 ← do let r ← na.remove (u8 37); c.union r
  let s6 ← do
    let n ← ascii_set.AsciiSet.Insts.CoreOpsBitNotAsciiSet.not c0
    ascii_set.AsciiSet.Insts.CoreOpsArithAddAsciiSetAsciiSet.add n c0
  pure [c0, na0, s2, s3, s4, s5, s6]

def mask (s : ascii_set.AsciiSet) : Result String := do
  let es ← (List.range 128).mapM (fun b => ascii_set.AsciiSet.should_percent_encode s (u8 b))
  let bits := (List.range 128).zip es
  pure (toHex ((List.range 16).map fun k =>
    (bits.filter (fun p => p.1 / 8 = k ∧ p.2)).foldl (fun acc p => acc + 2 ^ (p.1 % 8)) 0))

/-- Run the encoder iterator to the end: (number of chunks, concatenated bytes). -/
def collectEnc : Nat → PercentEncode → Result (Nat × List Nat)
  | 0, _ => fail .panic
  | f + 1, it => do
    let (o, it') ← PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.next it
    match o with
    | none => pure (0, [])
    | some c => do let (n, l) ← collectEnc f it'; pure (n + 1, bytesOf c ++ l)

def collectDec : Nat → PercentDecode → Result (List Nat)
  | 0, _ => fail .panic
  | f + 1, d => do
    let (o, d') ← PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.next d
    match o with
    | none => pure []
    | some b => do let l ← collectDec f d'; pure (b.val :: l)

def bufWrite : core.fmt.Write (List Nat) :=
  { write_str := fun buf s => ok (.Ok (), buf ++ bytesOf s) }

def encLine (sets : List ascii_set.AsciiSet) (input : String) : String :=
  match input.splitOn "," with
  | [si, h] =>
    let bs := unhex h
    match sets[dec si]? with
    | none => "bad set"
    | some set =>
    show? (α := String) (do
      let it ← percent_encode (sl bs) set
      let (lo, hi) ← PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.size_hint it
      let (n, joined) ← collectEnc (bs.length + 2) it
      let (r, disp) ← write_chunks bufWrite (sl bs) set []
      let cow ← alloc.borrow.CowAStrString.Insts.CoreConvertFromPercentEncode.from it
      let var := match cow with | .Borrowed _ => "B" | .Owned _ => "O"
      let cowOk := (cowStr cow).drop 1 == toHex joined
      let dispOk := disp == joined && (match r with | .Ok _ => true | .Err _ => false)
      pure (s!"{n};{toHex joined};{var};{lo.val},{hi.map (·.val) |>.getD 0}" ++
        (if cowOk && dispOk then "" else s!" (cow/display mismatch: {cowStr cow} {toHex disp})")))
      id
  | _ => "bad input"

def decLine (h : String) : String :=
  let bs := unhex h
  show? (α := String) (do
    let d ← percent_decode (sl bs)
    let (lo, hi) ← PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.size_hint d
    let l ← collectDec (bs.length + 2) d
    let cow ← alloc.borrow.CowASliceU8VecU8.Insts.CoreConvertFromPercentDecode.from d
    let cv := match cow with | .Borrowed _ => "B" | .Owned _ => "O"
    let cowBytes := match cow with | .Borrowed s => bytesOf s | .Owned v => v.val.map (·.val)
    let u ← PercentDecode.decode_utf8 d
    let us := match u with | .Ok c => "V" ++ cowStr c | .Err _ => "I"
    let lossy ← PercentDecode.decode_utf8_lossy d
    pure (s!"{toHex l};{cv};{us};{cowStr lossy};{lo.val},{hi.map (·.val) |>.getD 0}" ++
      (if cowBytes == l then "" else " (cow bytes mismatch)"))) id

def main (args : List String) : IO UInt32 := do
  let lines ← IO.FS.lines (args.headD "cross.txt")
  let some sets := (match mkSets.match with | .ok s => some s | _ => none)
    | IO.println "building the sets failed"; return 1
  let mut fails := 0
  let mut counts : Std.HashMap String Nat := {}
  for line in lines do
    match line.splitOn "|" with
    | [kind, input, expected] =>
      counts := counts.insert kind (counts.getD kind 0 + 1)
      let got := match kind with
        | "set" => match sets[dec input]? with
          | some st => show? (mask st) id
          | none => "bad set"
        | "addrm" =>
          let b := u8 (unhex input).head!
          show? (ascii_set.CONTROLS) (fun c =>
            (show? (c.add b) (fun _ => "-")) ++ (show? (c.remove b) (fun _ => "-")))
        | "enc" => encLine sets input
        | "dec" => decLine input
        | _ => "unknown kind"
      if got != expected then
        fails := fails + 1
        if fails ≤ 20 then IO.println s!"FAIL {kind} {input}: Lean {got}, Rust {expected}"
    | _ => pure ()
  for (k, n) in counts.toList do IO.println s!"{k}: {n} vectors"
  IO.println s!"failures: {fails}"
  return (if fails = 0 then 0 else 1)
