/- Differential check of the hand-written x86 intrinsic models (variants/x86_64*/Crc32fast/External)
   against the real CPU. Reads lines from x86gen (`nm imm arg.. expected`, hex) on stdin and
   evaluates the Lean model on the same arguments. Run inside a built x86 variant project:
     x86gen 300 | lake env lean --run ModelCheck.lean
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

/-- The model's answer as a number, or none if the model fails or the nm is unknown. -/
def model (nm : String) (imm : Nat) (a : Array Nat) : Option Nat := do
  let r (w : Nat) (x : Option (BitVec w)) : Option Nat := x.map (·.toNat)
  match nm with
  | "xor128" => r 128 (res (core.core_arch.x86.sse2._mm_xor_si128 (b 128 a[0]!) (b 128 a[1]!)))
  | "and128" => r 128 (res (core.core_arch.x86.sse2._mm_and_si128 (b 128 a[0]!) (b 128 a[1]!)))
  | "add_epi8" => r 128 (res (core.core_arch.x86.sse2._mm_add_epi8 (b 128 a[0]!) (b 128 a[1]!)))
  | "shuffle_epi8" => r 128 (res (core.core_arch.x86.ssse3._mm_shuffle_epi8 (b 128 a[0]!) (b 128 a[1]!)))
  | "cvtsi32" => r 128 (res (core.core_arch.x86.sse2._mm_cvtsi32_si128 (i32 a[0]!)))
  | "set_epi64x" => r 128 (res (core.core_arch.x86.sse2._mm_set_epi64x (i64 a[0]!) (i64 a[1]!)))
  | "set_epi32" => r 128 (res (core.core_arch.x86.sse2._mm_set_epi32 (i32 a[0]!) (i32 a[1]!) (i32 a[2]!) (i32 a[3]!)))
  | "set1_epi8" => r 128 (res (core.core_arch.x86.sse2._mm_set1_epi8 (i8 a[0]!)))
  | "setr_epi8" =>
    let e := fun k => i8 a[k]!
    r 128 (res (core.core_arch.x86.sse2._mm_setr_epi8 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) (e 8) (e 9)
      (e 10) (e 11) (e 12) (e 13) (e 14) (e 15)))
  | "srli_si128" => r 128 (res (core.core_arch.x86.sse2._mm_srli_si128 (i32 imm) (b 128 a[0]!)))
  | "extract_epi32" => (res (core.core_arch.x86.sse41._mm_extract_epi32 (i32 imm) (b 128 a[0]!))).map (·.bv.toNat)
  | "clmul128" => r 128 (res (core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 (i32 imm) (b 128 a[0]!) (b 128 a[1]!)))
  | "set256_epi64x" => r 256 (res (core.core_arch.x86.avx._mm256_set_epi64x (i64 a[0]!) (i64 a[1]!) (i64 a[2]!) (i64 a[3]!)))
  | "cast256_128" => r 128 (res (core.core_arch.x86.avx._mm256_castsi256_si128 (b 256 a[0]!)))
  | "cast128_256" => r 256 (res (core.core_arch.x86.avx._mm256_castsi128_si256 (b 128 a[0]!)))
  | "extracti128" => r 128 (res (core.core_arch.x86.avx2._mm256_extracti128_si256 (i32 imm) (b 256 a[0]!)))
  | "xor256" => r 256 (res (core.core_arch.x86.avx2._mm256_xor_si256 (b 256 a[0]!) (b 256 a[1]!)))
  | "clmul256" => r 256 (res (core.core_arch.x86.vpclmulqdq._mm256_clmulepi64_epi128 (i32 imm) (b 256 a[0]!) (b 256 a[1]!)))
  | "set512_epi64" =>
    let e := fun k => i64 a[k]!
    r 512 (res (core.core_arch.x86.avx512f._mm512_set_epi64 (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) (e 7)))
  | "extracti32x4" => r 128 (res (core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 (i32 imm) (b 512 a[0]!)))
  | "cast128_512" => r 512 (res (core.core_arch.x86.avx512f._mm512_castsi128_si512 (b 128 a[0]!)))
  | "cast512_128" => r 128 (res (core.core_arch.x86.avx512f._mm512_castsi512_si128 (b 512 a[0]!)))
  | "xor512" => r 512 (res (core.core_arch.x86.avx512f._mm512_xor_si512 (b 512 a[0]!) (b 512 a[1]!)))
  | "clmul512" => r 512 (res (core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 (i32 imm) (b 512 a[0]!) (b 512 a[1]!)))
  | "load128" => do let s ← slice (a.toList.map fun n => ⟨BitVec.ofNat 8 n⟩); r 128 (res (specialized.pclmulqdq.load128 s))
  | "load256" => do let s ← slice (a.toList.map fun n => ⟨BitVec.ofNat 8 n⟩); r 256 (res (specialized.pclmulqdq.load256 s))
  | "load512" => do let s ← slice (a.toList.map fun n => ⟨BitVec.ofNat 8 n⟩); r 512 (res (specialized.pclmulqdq.load512 s))
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
  return (if bad == 0 && n > 0 && seen.size == 27 then 0 else 1)
