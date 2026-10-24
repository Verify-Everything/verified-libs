import Crc32fast.Baseline
import Crc32fast.Detect

/-!
# What differs between builds: the kernel behind `State`

`HasherFull.lean` is the same for every build; this file proves the two facts it needs about
`State` on this build. `Detect.lean` says what `State::new` returns.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

/-- There is no kernel on this build: `State` has no values. -/
theorem state_update_eq (s : specialized.State) (st : U32) (buf : Slice U8) :
    s.update st buf = ok ⟨update st.bv (bytes buf.val)⟩ := nomatch s

theorem state_clone_eq (s : specialized.State) :
    specialized.State.Insts.CoreCloneClone.clone s = ok s := nomatch s

end Crc32fastVerif
