-- [crc32fast]: external functions.
-- Hand-written models of the external functions (filled in from FunsExternal_Template.lean).
-- Every model below follows the Rust standard library documentation for that function.
module
public import Aeneas
public import Crc32fast.Extracted.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.internalConstructors false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open crc32fast


/-! Formatting, following `core/src/fmt/builders.rs`. `core::fmt::Formatter` is an opaque type in
    the Aeneas library, so the output sink is an opaque function: writing a string returns the
    writer's result (an `fmt::Write` impl may fail) and the formatter after the write. -/

/-- `Formatter::write_str` as seen by the builders: the result and the formatter afterwards. -/
opaque core.fmt.Formatter.sink : core.fmt.Formatter → Str →
    core.result.Result Unit core.fmt.Error × core.fmt.Formatter := fun f _ => (.Ok (), f)

/-- `Formatter::alternate()` (the `{:#?}` flag). -/
opaque core.fmt.Formatter.isPretty : core.fmt.Formatter → Bool := fun _ => false

/-- `debug_struct_new`: writes the name now, no fields yet. The back function returns the
    formatter the builder borrowed. -/
@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct"]
def core.fmt.Formatter.debug_struct (f : core.fmt.Formatter) (nm : Str) :
    Result (core.fmt.builders.DebugStruct × (core.fmt.builders.DebugStruct → core.fmt.Formatter)) :=
  let (r, f') := core.fmt.Formatter.sink f nm
  ok ({ fmt := f', result := r, has_fields := false }, fun ds => ds.fmt)

/-- `DebugStruct::finish`: closes the braces only if a field was written, then returns the result. -/
@[rust_fun
  "core::fmt::builders::{core::fmt::builders::DebugStruct<'a, 'b>}::finish"]
def core.fmt.builders.DebugStruct.finish (ds : core.fmt.builders.DebugStruct) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.builders.DebugStruct ×
      (core.fmt.builders.DebugStruct → core.fmt.builders.DebugStruct)) :=
  if ds.has_fields then
    match ds.result with
    | .Ok () =>
      let (r, f') := core.fmt.Formatter.sink ds.fmt
        (if core.fmt.Formatter.isPretty ds.fmt then toStr "}" else toStr " }")
      ok (r, { ds with fmt := f', result := r }, id)
    | .Err e => ok (.Err e, ds, id)
  else ok (ds.result, ds, id)

/-! Models used by the verified code. -/

/-- `u32::wrapping_neg`: two's-complement negation modulo 2^32. Never panics. -/
@[rust_fun "core::num::{u32}::wrapping_neg"]
def core.num.U32.wrapping_neg (x : Std.U32) : Result Std.U32 :=
  ok ⟨ - x.bv ⟩

/-- `Option::unwrap_or_else`: the contained value, or the closure's result. -/
@[rust_fun "core::option::{core::option::Option<@T>}::unwrap_or_else"]
def core.option.Option.unwrap_or_else
  {T : Type _} {F : Type _} (opsfunctionFnOnceFTupleTInst :
  core.ops.function.FnOnce F Unit T) :
  Option T → F → Result T
  | some x, _ => ok x
  | none, f => opsfunctionFnOnceFTupleTInst.call_once f ()

/-- `Option::clone`: clones the contained value, if any. -/
@[rust_fun
  "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone
  {T : Type _} (cloneCloneInst : core.clone.Clone T) :
  Option T → Result (Option T)
  | none => ok none
  | some x => do let y ← cloneCloneInst.clone x; ok (some y)

/-- `Option::branch` (the `?` operator): `Some v` continues with `v`, `None` breaks. -/
@[rust_fun
  "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch
  {T : Type _} :
  Option T → Result (core.ops.control_flow.ControlFlow (Option Never) T)
  | some v => ok (.Continue v)
  | none => ok (.Break none)

/-- `Option::from_residual`: the residual of `?` on `Option` is always `None`. -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def
  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual
  (T : Type _) : Option Never → Result (Option T)
  | _ => ok none

/-! ## x86 SIMD intrinsics

Pure models first (namespace `x86`), then the Rust functions as `ok (model ...)`.
Each model follows Intel's Intrinsics Guide and the Rust `core::arch` source
(`library/stdarch/crates/core_arch/src/x86`). Registers are bit vectors with byte `k` at
bits `8k .. 8k+7` (little endian, as loaded from memory). -/

namespace x86

/-- Byte `k` of a register. -/
def byte {w : Nat} (x : BitVec w) (k : Nat) : BitVec 8 := (x >>> (8 * k)).setWidth 8

/-- A register built from bytes in memory order (missing bytes are zero). -/
def fromBytes (w : Nat) : List (BitVec 8) → BitVec w
  | [] => 0#w
  | b :: l => b.setWidth w ^^^ (fromBytes w l <<< 8)

/-- 128-bit lane `k` of a wide register. -/
def lane {w : Nat} (x : BitVec w) (k : Nat) : BitVec 128 := (x >>> (128 * k)).setWidth 128

def lo64 (x : BitVec 128) : BitVec 64 := x.setWidth 64
def hi64 (x : BitVec 128) : BitVec 64 := (x >>> 64).setWidth 64

/-- Carry-less product of the low `n` bits of `a` with `b`. -/
def clmulN (a b : BitVec 64) : Nat → BitVec 128
  | 0 => 0#128
  | n + 1 => clmulN a b n ^^^ (if a.getLsbD n then b.setWidth 128 <<< n else 0#128)

/-- `PCLMULQDQ`: 64 x 64 -> 128 carry-less multiply. -/
def clmul (a b : BitVec 64) : BitVec 128 := clmulN a b 64

/-- `_mm_clmulepi64_si128`: imm bit 0 picks the qword of `a`, bit 4 the qword of `b`. -/
def clmulSel (imm : BitVec 32) (a b : BitVec 128) : BitVec 128 :=
  clmul (if imm.getLsbD 0 then hi64 a else lo64 a) (if imm.getLsbD 4 then hi64 b else lo64 b)

/-- Apply a lane operation to every 128-bit lane of an `n`-lane register. -/
def perLane2 (n : Nat) (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec (128 * n)) :
    BitVec (128 * n) :=
  (List.range n).foldl (fun acc k => acc ||| ((f (lane a k) (lane b k)).setWidth (128 * n) <<< (128 * k)))
    0#(128 * n)

/-- `_mm_shuffle_epi8`: byte `i` of the result is 0 if bit 7 of `b[i]` is set, else
    `a[b[i] & 15]`. -/
def shuffle (a b : BitVec 128) : BitVec 128 :=
  fromBytes 128 ((List.range 16).map fun i =>
    let c := byte b i
    if c.getLsbD 7 then 0#8 else byte a (c.toNat % 16))

/-- `_mm_add_epi8`: bytewise wrapping add. -/
def addBytes (a b : BitVec 128) : BitVec 128 :=
  fromBytes 128 ((List.range 16).map fun i => byte a i + byte b i)

/-- `_mm_srli_si128`: shift right by `imm` bytes; 0 if `imm > 15` (imm is taken mod 256). -/
def srliBytes (imm : BitVec 32) (a : BitVec 128) : BitVec 128 :=
  if imm.toNat % 256 > 15 then 0#128 else a >>> (8 * (imm.toNat % 256))

/-- `_mm_extract_epi32`: dword `imm & 3`. -/
def extract32 (imm : BitVec 32) (a : BitVec 128) : BitVec 32 :=
  (a >>> (32 * (imm.toNat % 4))).setWidth 32

end x86

open x86

@[rust_fun "core::core_arch::x86::sse2::_mm_xor_si128"]
def core.core_arch.x86.sse2._mm_xor_si128 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := ok (a ^^^ b)

@[rust_fun "core::core_arch::x86::sse2::_mm_and_si128"]
def core.core_arch.x86.sse2._mm_and_si128 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := ok (a &&& b)

@[rust_fun "core::core_arch::x86::sse2::_mm_add_epi8"]
def core.core_arch.x86.sse2._mm_add_epi8 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := ok (addBytes a b)

/-- `_mm_cvtsi32_si128`: the 32-bit value in the low dword, the rest zero. -/
@[rust_fun "core::core_arch::x86::sse2::_mm_cvtsi32_si128"]
def core.core_arch.x86.sse2._mm_cvtsi32_si128 (a : Std.I32) :
    Result core.core_arch.x86.__m128i := ok (a.bv.setWidth 128)

/-- `_mm_set_epi64x(e1, e0)`: `e0` is the low qword. -/
@[rust_fun "core::core_arch::x86::sse2::_mm_set_epi64x"]
def core.core_arch.x86.sse2._mm_set_epi64x (e1 e0 : Std.I64) :
    Result core.core_arch.x86.__m128i := ok (e1.bv ++ e0.bv)

/-- `_mm_set_epi32(e3, e2, e1, e0)`: `e0` is the low dword. -/
@[rust_fun "core::core_arch::x86::sse2::_mm_set_epi32"]
def core.core_arch.x86.sse2._mm_set_epi32 (e3 e2 e1 e0 : Std.I32) :
    Result core.core_arch.x86.__m128i := ok (e3.bv ++ e2.bv ++ e1.bv ++ e0.bv)

@[rust_fun "core::core_arch::x86::sse2::_mm_set1_epi8"]
def core.core_arch.x86.sse2._mm_set1_epi8 (a : Std.I8) :
    Result core.core_arch.x86.__m128i := ok (fromBytes 128 (List.replicate 16 a.bv))

/-- `_mm_setr_epi8(e0, ..., e15)`: `e0` is byte 0. -/
@[rust_fun "core::core_arch::x86::sse2::_mm_setr_epi8"]
def core.core_arch.x86.sse2._mm_setr_epi8
    (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 : Std.I8) :
    Result core.core_arch.x86.__m128i :=
  ok (fromBytes 128 [e0.bv, e1.bv, e2.bv, e3.bv, e4.bv, e5.bv, e6.bv, e7.bv, e8.bv, e9.bv,
    e10.bv, e11.bv, e12.bv, e13.bv, e14.bv, e15.bv])

@[rust_fun "core::core_arch::x86::sse2::_mm_srli_si128"]
def core.core_arch.x86.sse2._mm_srli_si128 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := ok (srliBytes IMM8.bv a)

@[rust_fun "core::core_arch::x86::sse41::_mm_extract_epi32"]
def core.core_arch.x86.sse41._mm_extract_epi32 (IMM8 : Std.I32) (a : core.core_arch.x86.__m128i) :
    Result Std.I32 := ok ⟨extract32 IMM8.bv a⟩

@[rust_fun "core::core_arch::x86::ssse3::_mm_shuffle_epi8"]
def core.core_arch.x86.ssse3._mm_shuffle_epi8 (a b : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := ok (shuffle a b)

@[rust_fun "core::core_arch::x86::pclmulqdq::_mm_clmulepi64_si128"]
def core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 (IMM8 : Std.I32)
    (a b : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i :=
  ok (clmulSel IMM8.bv a b)

/-! 256-bit (AVX, AVX2, VPCLMULQDQ). -/

/-- `_mm256_set_epi64x(e3, e2, e1, e0)`: `e0` is the low qword. -/
@[rust_fun "core::core_arch::x86::avx::_mm256_set_epi64x"]
def core.core_arch.x86.avx._mm256_set_epi64x (e3 e2 e1 e0 : Std.I64) :
    Result core.core_arch.x86.__m256i := ok (e3.bv ++ e2.bv ++ e1.bv ++ e0.bv)

@[rust_fun "core::core_arch::x86::avx::_mm256_castsi256_si128"]
def core.core_arch.x86.avx._mm256_castsi256_si128 (a : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m128i := ok (a.setWidth 128)

/-- ASSUMPTION: the upper lane is zero. Intel leaves it undefined; Rust's stdarch (the pinned
    nightly) fills it from `i64x2::ZERO`. -/
@[rust_fun "core::core_arch::x86::avx::_mm256_castsi128_si256"]
def core.core_arch.x86.avx._mm256_castsi128_si256 (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m256i := ok (a.setWidth 256)

@[rust_fun "core::core_arch::x86::avx2::_mm256_extracti128_si256"]
def core.core_arch.x86.avx2._mm256_extracti128_si256 (IMM1 : Std.I32)
    (a : core.core_arch.x86.__m256i) : Result core.core_arch.x86.__m128i :=
  ok (lane a (IMM1.bv.toNat % 2))

@[rust_fun "core::core_arch::x86::avx2::_mm256_xor_si256"]
def core.core_arch.x86.avx2._mm256_xor_si256 (a b : core.core_arch.x86.__m256i) :
    Result core.core_arch.x86.__m256i := ok (a ^^^ b)

@[rust_fun "core::core_arch::x86::vpclmulqdq::_mm256_clmulepi64_epi128"]
def core.core_arch.x86.vpclmulqdq._mm256_clmulepi64_epi128 (IMM8 : Std.I32)
    (a b : core.core_arch.x86.__m256i) : Result core.core_arch.x86.__m256i :=
  ok (perLane2 2 (clmulSel IMM8.bv) a b)

/-! 512-bit (AVX-512F, VPCLMULQDQ). -/

/-- `_mm512_set_epi64(e7, ..., e0)`: `e0` is the low qword. -/
@[rust_fun "core::core_arch::x86::avx512f::_mm512_set_epi64"]
def core.core_arch.x86.avx512f._mm512_set_epi64 (e7 e6 e5 e4 e3 e2 e1 e0 : Std.I64) :
    Result core.core_arch.x86.__m512i :=
  ok (e7.bv ++ e6.bv ++ e5.bv ++ e4.bv ++ e3.bv ++ e2.bv ++ e1.bv ++ e0.bv)

@[rust_fun "core::core_arch::x86::avx512f::_mm512_extracti32x4_epi32"]
def core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 (IMM2 : Std.I32)
    (a : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m128i :=
  ok (lane a (IMM2.bv.toNat % 4))

/-- ASSUMPTION: the upper 384 bits are zero. Intel leaves them undefined; Rust documents them
    as "non-deterministically set to some valid value" and today fills them from
    `_mm_undefined_si128()`, which returns zeros. -/
@[rust_fun "core::core_arch::x86::avx512f::_mm512_castsi128_si512"]
def core.core_arch.x86.avx512f._mm512_castsi128_si512 (a : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m512i := ok (a.setWidth 512)

@[rust_fun "core::core_arch::x86::avx512f::_mm512_castsi512_si128"]
def core.core_arch.x86.avx512f._mm512_castsi512_si128 (a : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m128i := ok (a.setWidth 128)

@[rust_fun "core::core_arch::x86::avx512f::_mm512_xor_si512"]
def core.core_arch.x86.avx512f._mm512_xor_si512 (a b : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i := ok (a ^^^ b)

@[rust_fun "core::core_arch::x86::vpclmulqdq::_mm512_clmulepi64_epi128"]
def core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 (IMM8 : Std.I32)
    (a b : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i :=
  ok (perLane2 4 (clmulSel IMM8.bv) a b)

/-! The three load helpers added by the verification patch (`_mm_loadu_si128` and friends on the
    first 16/32/64 bytes of the slice). Too-short slices are a failure, so the proofs show they
    never happen. -/

def specialized.pclmulqdq.load128 (a : Slice Std.U8) : Result core.core_arch.x86.__m128i :=
  if 16 ≤ a.length then ok (fromBytes 128 ((a.val.take 16).map (·.bv))) else fail .panic

def specialized.pclmulqdq.load256 (a : Slice Std.U8) : Result core.core_arch.x86.__m256i :=
  if 32 ≤ a.length then ok (fromBytes 256 ((a.val.take 32).map (·.bv))) else fail .panic

def specialized.pclmulqdq.load512 (a : Slice Std.U8) : Result core.core_arch.x86.__m512i :=
  if 64 ≤ a.length then ok (fromBytes 512 ((a.val.take 64).map (·.bv))) else fail .panic

/-! CPU feature detection (`std` build). `is_x86_feature_detected!` reads a cache that std fills
    from CPUID on first use. The model is a fixed but unknown feature set: `cpuHas` is opaque, so
    the proofs hold for every CPU. -/

inductive x86.Feature where
  | pclmulqdq | sse2 | sse4_1 | ssse3 | avx2 | avx512f | vpclmulqdq
  deriving DecidableEq

/-- Whether the running CPU (and OS) supports a feature. -/
opaque x86.cpuHas : x86.Feature → Bool := fun _ => false

@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::pclmulqdq"]
def std_detect.detect.arch.x86.__is_feature_detected.pclmulqdq : Result Bool := ok (x86.cpuHas .pclmulqdq)
@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::sse2"]
def std_detect.detect.arch.x86.__is_feature_detected.sse2 : Result Bool := ok (x86.cpuHas .sse2)
@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::sse4_1"]
def std_detect.detect.arch.x86.__is_feature_detected.sse4_1 : Result Bool := ok (x86.cpuHas .sse4_1)
@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::ssse3"]
def std_detect.detect.arch.x86.__is_feature_detected.ssse3 : Result Bool := ok (x86.cpuHas .ssse3)
@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::avx2"]
def std_detect.detect.arch.x86.__is_feature_detected.avx2 : Result Bool := ok (x86.cpuHas .avx2)
@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::avx512f"]
def std_detect.detect.arch.x86.__is_feature_detected.avx512f : Result Bool := ok (x86.cpuHas .avx512f)
@[rust_fun "std_detect::detect::arch::x86::__is_feature_detected::vpclmulqdq"]
def std_detect.detect.arch.x86.__is_feature_detected.vpclmulqdq : Result Bool :=
  ok (x86.cpuHas .vpclmulqdq)
