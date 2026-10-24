-- [crc32fast]: external types.
-- External types.
module
public import Aeneas
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

/-- [core::fmt::builders::DebugStruct]
    Source: '/rustc/library/core/src/fmt/builders.rs', lines 112:0-112:34
    Name pattern: [core::fmt::builders::DebugStruct]
    Visibility: public -/
@[rust_type "core::fmt::builders::DebugStruct" (mutRegions := #[0])]
structure core.fmt.builders.DebugStruct where
  /-- The formatter being written to (Rust: `fmt: &mut Formatter`). -/
  fmt : core.fmt.Formatter
  /-- The result of the writes so far. -/
  result : core.result.Result Unit core.fmt.Error
  /-- Whether `field` was called. -/
  has_fields : Bool

/-! SIMD register types: plain bit vectors (bit `i` of the register is bit `i` of the vector,
    so byte `k` in memory order is bits `8k .. 8k+7`). -/

@[rust_type "core::core_arch::x86::__m128i"]
abbrev core.core_arch.x86.__m128i : Type := BitVec 128

@[rust_type "core::core_arch::x86::__m256i"]
abbrev core.core_arch.x86.__m256i : Type := BitVec 256

@[rust_type "core::core_arch::x86::__m512i"]
abbrev core.core_arch.x86.__m512i : Type := BitVec 512
