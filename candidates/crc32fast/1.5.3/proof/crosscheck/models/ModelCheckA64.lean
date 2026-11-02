/- Differential check of the aarch64 CRC32B/CRC32X models (variants/aarch64*/Crc32fast/External)
   against the CPU (or qemu). Reads lines from a64gen on stdin. Run inside a built aarch64 variant:
     a64gen 1000 | lake env lean --run ModelCheckA64.lean
   Exit code 0 iff every line matches. -/
import Crc32fast.External.FunsExternal
open Aeneas Aeneas.Std Result

def hex (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0)) 0

def i32 (n : Nat) : I32 := ⟨BitVec.ofNat 32 n⟩
def i64 (n : Nat) : I64 := ⟨BitVec.ofNat 64 n⟩
def i8 (n : Nat) : I8 := ⟨BitVec.ofNat 8 n⟩
def b (w n : Nat) : BitVec w := BitVec.ofNat w n

def res {α} (r : Result α) : Option α :=
  match Result.match r with
  | .ok v => some v
  | _ => none

def slice (l : List U8) : Option (Slice U8) :=
  if h : l.length ≤ Usize.max then some (Slice.from l h) else none

/-- The model's answer as a number, or none if the model fails or the name is unknown. -/
def model (nm : String) (_imm : Nat) (a : Array Nat) : Option Nat :=
  let c : U32 := ⟨BitVec.ofNat 32 a[0]!⟩
  match nm with
  | "crc32b" => (res (core.core_arch.arm_shared.neon.generated.__crc32b c ⟨BitVec.ofNat 8 a[1]!⟩)).map (·.bv.toNat)
  | "crc32d" => (res (core.core_arch.aarch64.neon.generated.__crc32d c ⟨BitVec.ofNat 64 a[1]!⟩)).map (·.bv.toNat)
  | _ => none

partial def loop (h : IO.FS.Stream) (n bad : Nat) (seen : Std.HashMap String Nat) :
    IO (Nat × Nat × Std.HashMap String Nat) := do
  let line ← h.getLine
  if line.isEmpty then return (n, bad, seen)
  let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "") |>.toArray
  if ws.size < 3 then return ← loop h n bad seen
  let nm := ws[0]!; let imm := ws[1]!.toNat!
  let args := (ws.extract 2 (ws.size - 1)).map hex
  let want := hex ws[ws.size - 1]!
  let got := model nm imm args
  let seen := seen.insert nm (seen.getD nm 0 + 1)
  if got != some want then
    IO.println s!"MISMATCH {nm} imm={imm}: cpu={want} model={got}"
    loop h (n + 1) (bad + 1) seen
  else loop h (n + 1) bad seen

def main : IO UInt32 := do
  let (n, bad, seen) ← loop (← IO.getStdin) 0 0 {}
  IO.println s!"{n} lines, {bad} mismatches, {seen.size} intrinsics: {seen.toList.map (·.1) |>.mergeSort}"
  return (if bad == 0 && n > 0 && seen.size == 2 then 0 else 1)
