import Crc32fast.Extracted.Funs

/-!
# CPU feature detection, `std` build

`State::detect` asks `is_x86_feature_detected!` at run time. `sse2` needs no check: it is part of
x86_64 itself, so rustc folds that test to `true`. The proofs hold for every value of `cpuHas`.
-/

open Aeneas Aeneas.Std Result crc32fast x86

namespace Crc32fastVerif

/-- The kernel the crate should pick: the widest one whose instructions the CPU has. -/
def bestKind : Option specialized.pclmulqdq.Kind :=
  if cpuHas .pclmulqdq && cpuHas .sse4_1 && cpuHas .ssse3 then
    if cpuHas .avx512f && cpuHas .vpclmulqdq then some .Avx512
    else if cpuHas .avx2 && cpuHas .vpclmulqdq then some .Avx2
    else some .Sse
  else none

/-- What `State::new` returns on this build. -/
def newState : Option specialized.pclmulqdq.State := bestKind.map fun k => { kind := k }

theorem detect_eq : specialized.pclmulqdq.State.detect = ok bestKind := by
  unfold specialized.pclmulqdq.State.detect bestKind
  simp only [std_detect.detect.arch.x86.__is_feature_detected.pclmulqdq,
    std_detect.detect.arch.x86.__is_feature_detected.sse4_1,
    std_detect.detect.arch.x86.__is_feature_detected.ssse3,
    std_detect.detect.arch.x86.__is_feature_detected.avx512f,
    std_detect.detect.arch.x86.__is_feature_detected.avx2,
    std_detect.detect.arch.x86.__is_feature_detected.vpclmulqdq, bind_ok]
  cases cpuHas .pclmulqdq <;> cases cpuHas .sse4_1 <;> cases cpuHas .ssse3 <;>
    cases cpuHas .avx512f <;> cases cpuHas .avx2 <;> cases cpuHas .vpclmulqdq <;> rfl

/-- The instructions each kernel uses (its `#[target_feature]` list, `sse2` aside). -/
def needs : specialized.pclmulqdq.Kind → List Feature
  | .Sse => [.pclmulqdq, .sse4_1, .ssse3]
  | .Avx2 => [.pclmulqdq, .sse4_1, .ssse3, .avx2, .vpclmulqdq]
  | .Avx512 => [.pclmulqdq, .sse4_1, .ssse3, .avx2, .vpclmulqdq, .avx512f]

/-- Safety of the `unsafe` kernel calls: detection only picks a kernel whose instructions the CPU
    reports. (`calculate_avx512` also enables `avx2`; on real CPUs AVX-512F implies AVX2, which this
    check does not test. The crate relies on that implication.) -/
theorem detect_safe (k : specialized.pclmulqdq.Kind) (h : bestKind = some k) :
    ∀ f ∈ needs k, f = .avx2 ∧ k = .Avx512 ∨ cpuHas f = true := by
  unfold bestKind at h
  cases k <;> intro f hf <;> simp only [needs, List.mem_cons, List.not_mem_nil, or_false] at hf <;>
    revert h <;>
    cases h1 : cpuHas .pclmulqdq <;> cases h2 : cpuHas .sse4_1 <;> cases h3 : cpuHas .ssse3 <;>
    cases h4 : cpuHas .avx512f <;> cases h5 : cpuHas .avx2 <;> cases h6 : cpuHas .vpclmulqdq <;>
    simp <;> rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem state_new_eq : specialized.pclmulqdq.State.new = ok newState := by
  unfold specialized.pclmulqdq.State.new
  rw [detect_eq, bind_ok]
  unfold newState
  generalize bestKind = o
  rcases o with _ | k <;>
    simp only [core.option.Option.map, Option.map,
      specialized.pclmulqdq.State.new.closure.Insts.CoreOpsFunctionFnOnceTupleKindState,
      specialized.pclmulqdq.State.new.closure.Insts.CoreOpsFunctionFnOnceTupleKindState.call_once, bind_ok,
      bind_tc_ok]

end Crc32fastVerif
