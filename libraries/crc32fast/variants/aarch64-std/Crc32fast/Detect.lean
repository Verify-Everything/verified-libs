import Crc32fast.Extracted.Funs

/-!
# CPU feature detection, aarch64 `std` build

With `std`, `State::new` asks `is_aarch64_feature_detected!("crc")` at run time. The answer is an
opaque `a64.cpuHasCrc`, so every theorem holds whichever kernel the CPU gets.
-/

open Aeneas Aeneas.Std Result crc32fast

namespace Crc32fastVerif

/-- What `State::new` returns on this build. -/
def newState : Option specialized.aarch64.State := if a64.cpuHasCrc then some () else none

theorem state_new_eq : specialized.aarch64.State.new = ok newState := by
  unfold specialized.aarch64.State.new newState
  simp only [std_detect.detect.arch.aarch64.__is_feature_detected.crc, bind_tc_ok, bind_ok]
  cases a64.cpuHasCrc <;> rfl

end Crc32fastVerif
