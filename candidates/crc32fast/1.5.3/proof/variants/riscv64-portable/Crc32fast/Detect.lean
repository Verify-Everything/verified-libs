import Crc32fast.Extracted.Funs

/-!
# The portable build (riscv64 and every target without a SIMD kernel)

`specialized::State` is an empty enum here, so `State::new` is `None` and no kernel exists.
-/

open Aeneas Aeneas.Std Result crc32fast

namespace Crc32fastVerif

/-- What `State::new` returns on this build. -/
def newState : Option specialized.State := none

theorem state_new_eq : specialized.State.new = ok newState := rfl

end Crc32fastVerif
