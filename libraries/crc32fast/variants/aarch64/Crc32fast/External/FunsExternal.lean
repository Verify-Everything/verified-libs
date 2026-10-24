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

/-! ## Iterators -/

/-- `Iterator::fold` (default method): call `next` until `None`, threading the accumulator
    through the closure (`library/core/src/iter/traits/iterator.rs`). -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::fold"]
def core.iter.traits.iterator.Iterator.fold.default
  {Self : Type _} {B : Type _} {F : Type _} {Clause0_Item : Type _}
  (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
  (opsfunctionFnMutFPairBInst : core.ops.function.FnMut F (B × Clause0_Item) B)
  (it : Self) (init : B) (f : F) : Result B := do
  let (_, acc, _) ← loop (fun (p : Self × B × F) => do
      let (it, acc, f) := p
      let (o, it') ← IteratorInst.next it
      match o with
      | none => ok (ControlFlow.done (it', acc, f))
      | some x =>
        let (acc', f') ← opsfunctionFnMutFPairBInst.call_mut f (acc, x)
        ok (ControlFlow.cont (it', acc', f'))) (it, init, f)
  ok acc

/-- `slice::Iter::fold`: the closure over the elements not yet visited, in order. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::fold"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold
  {T : Type _} {B : Type _} {F : Type _}
  (opsfunctionFnMutFPairBSharedATBInst : core.ops.function.FnMut F (B × T) B)
  (it : core.slice.iter.Iter T) (init : B) (f : F) : Result B := do
  let (acc, _) ← (it.slice.val.drop it.i).foldlM
    (fun (p : B × F) x => opsfunctionFnMutFPairBSharedATBInst.call_mut p.2 (p.1, x)) (init, f)
  ok acc

/-! ## aarch64 CRC32 instructions and `align_to`

`CRC32B` and `CRC32X`, written as the Arm Architecture Reference Manual's pseudocode
(`CRC32B, CRC32H, CRC32W, CRC32X`, shared function `Poly32Mod2`):

    tempacc = BitReverse(acc) : Zeros(size)
    tempval = BitReverse(val) : Zeros(32)
    X[d]    = BitReverse(Poly32Mod2(tempacc EOR tempval, 0x04C11DB7))

The proofs show this equals the spec's bit-at-a-time `crcRaw` on the data bytes in memory order
(aarch64 Linux is little endian). -/

/-- Where `align_to` splits: it may pick any prefix length and any number of `u64`s that fit
    (Rust only promises that `prefix ++ middle ++ suffix` is the input). Opaque, so the proofs
    hold for every split. -/
opaque a64.splitPre : List Std.U8 → Nat := fun _ => 0
opaque a64.splitMid : List Std.U8 → Nat := fun _ => 0

namespace a64

/-- `Poly32Mod2` steps for bits `32 + k - 1` down to `32`: if bit `i` is set, XOR
    `poly : Zeros(i - 32)` into bits `i-1 .. 0`. -/
def polyMod {N : Nat} (poly : BitVec 32) : Nat → BitVec N → BitVec N
  | 0, d => d
  | k + 1, d =>
    let i := 32 + k
    polyMod poly k (if d.getLsbD i then d ^^^ ((poly.setWidth N) <<< k) else d)

/-- The Arm `CRC32` instruction on a `size`-bit value. -/
def crc32 {size : Nat} (acc : BitVec 32) (val : BitVec size) : BitVec 32 :=
  let tempacc : BitVec (32 + size) := acc.reverse ++ 0#size
  let tempval : BitVec (32 + size) := (val.reverse ++ 0#32).setWidth (32 + size)
  ((polyMod 0x04C11DB7#32 size (tempacc ^^^ tempval)).setWidth 32).reverse

/-- Byte `k` of a 64-bit value (little endian). -/
def byte (x : BitVec 64) (k : Nat) : BitVec 8 := (x >>> (8 * k)).setWidth 8

/-- The 8 bytes of a `u64` in memory order. -/
def le8 (x : Std.U64) : List (BitVec 8) := (List.range 8).map (byte x.bv)

/-- The `u64` that 8 bytes in memory order make (missing bytes are zero). -/
def ofBytes : List (BitVec 8) → BitVec 64
  | [] => 0#64
  | b :: l => b.setWidth 64 ^^^ (ofBytes l <<< 8)

/-- The `u64`s of a byte list, 8 bytes each. -/
def quadsOf : Nat → List Std.U8 → List Std.U64
  | 0, _ => []
  | n + 1, l => ⟨ofBytes ((l.take 8).map (·.bv))⟩ :: quadsOf n (l.drop 8)

end a64

/-- `__crc32d(crc, data)`: `CRC32X`. -/
@[rust_fun "core::core_arch::aarch64::neon::generated::__crc32d"]
def core.core_arch.aarch64.neon.generated.__crc32d (crc : Std.U32) (data : Std.U64) :
    Result Std.U32 := ok ⟨a64.crc32 crc.bv data.bv⟩

/-- `__crc32b(crc, data)`: `CRC32B`. -/
@[rust_fun "core::core_arch::arm_shared::neon::generated::__crc32b"]
def core.core_arch.arm_shared.neon.generated.__crc32b (crc : Std.U32) (data : Std.U8) :
    Result Std.U32 := ok ⟨a64.crc32 crc.bv data.bv⟩

/-- The patch's `split_quads(data) = data.align_to::<u64>()`: some prefix, then whole `u64`s,
    then the rest. -/
def specialized.aarch64.split_quads (data : Slice Std.U8) :
    Result ((Slice Std.U8) × (Slice Std.U64) × (Slice Std.U8)) :=
  have hl : data.val.length ≤ Usize.max := data.property
  let p := min (a64.splitPre data.val) data.val.length
  let m := min (a64.splitMid data.val) ((data.val.length - p) / 8)
  have hp : p ≤ data.val.length := Nat.min_le_right _ _
  have hm : m ≤ (data.val.length - p) / 8 := Nat.min_le_right _ _
  ok (Slice.from (data.val.take p) (by simp only [List.length_take]; omega),
      Slice.from (a64.quadsOf m (data.val.drop p)) (by
        have h : ∀ (k : Nat) (l : List Std.U8), (a64.quadsOf k l).length = k := by
          intro k
          induction k with
          | zero => intro l; rfl
          | succ k ih => intro l; simp [a64.quadsOf, ih]
        rw [h]; omega),
      Slice.from (data.val.drop (p + 8 * m)) (by simp only [List.length_drop]; omega))
