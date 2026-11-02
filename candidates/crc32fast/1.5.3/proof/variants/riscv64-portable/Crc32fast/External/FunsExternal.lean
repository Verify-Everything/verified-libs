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

