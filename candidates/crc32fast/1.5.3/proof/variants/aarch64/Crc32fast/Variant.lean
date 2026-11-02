import Crc32fast.Aarch64
import Crc32fast.Detect

/-!
# What differs between builds: the kernel behind `State`

`HasherFull.lean` is the same for every build; this file proves the two facts it needs about
`State` on this build. `Detect.lean` says what `State::new` returns.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

/-- `State::update` runs the aarch64 kernel, which computes the spec's `update`. -/
theorem state_update_eq (s : specialized.aarch64.State) (st : U32) (buf : Slice U8) :
    s.update st buf = ok ⟨update st.bv (bytes buf.val)⟩ := by
  unfold specialized.aarch64.State.update
  exact calculate_eq st buf

theorem state_clone_eq (s : specialized.aarch64.State) :
    specialized.aarch64.State.Insts.CoreCloneClone.clone s = ok s := by
  simp only [specialized.aarch64.State.Insts.CoreCloneClone.clone, BuiltinClone, bind_ok, bind_tc_ok]

end Crc32fastVerif
