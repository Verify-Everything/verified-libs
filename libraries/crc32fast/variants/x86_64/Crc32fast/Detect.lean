import Crc32fast.Extracted.Funs

/-!
# CPU feature detection, `no_std` build

Without `std`, `State::detect` uses compile-time `cfg!(target_feature = ...)`. For the default
`x86_64-unknown-linux-gnu` target `pclmulqdq` is not enabled at compile time, so it is `None` and
`Hasher` always uses the baseline kernel.
-/

open Aeneas Aeneas.Std Result crc32fast

namespace Crc32fastVerif

/-- What `State::new` returns on this build. -/
def newState : Option specialized.pclmulqdq.State := none

theorem detect_eq : specialized.pclmulqdq.State.detect = ok none := rfl

theorem state_new_eq : specialized.pclmulqdq.State.new = ok newState := by
  simp only [specialized.pclmulqdq.State.new, specialized.pclmulqdq.State.detect, core.option.Option.map,
    bind_ok, newState]

end Crc32fastVerif
