import Crc32fast.Extracted.Funs

/-!
# CPU feature detection, aarch64 `no_std` build

Without `std`, `State::new` uses compile-time `cfg!(target_feature = "crc")`. The default
`aarch64-unknown-linux-gnu` target does not enable `crc`, so it is `None` and `Hasher` uses the
baseline kernel. The `std` build replaces this file.
-/

open Aeneas Aeneas.Std Result crc32fast

namespace Crc32fastVerif

/-- What `State::new` returns on this build. -/
def newState : Option specialized.aarch64.State := none

theorem state_new_eq : specialized.aarch64.State.new = ok newState := rfl

end Crc32fastVerif
