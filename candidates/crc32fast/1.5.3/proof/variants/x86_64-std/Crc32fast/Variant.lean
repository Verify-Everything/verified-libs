import Crc32fast.SimdAvx
import Crc32fast.Detect

/-!
# What differs between builds: the kernel behind `State`

`HasherFull.lean` is the same for every build; this file proves the two facts it needs about
`State` on this build. `Detect.lean` says what `State::new` returns.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec x86

namespace Crc32fastVerif

/-- `State::update` computes the spec's `update` for each of the three kernels. -/
theorem state_update_eq (s : specialized.pclmulqdq.State) (st : U32) (buf : Slice U8) :
    s.update st buf = ok ⟨update st.bv (bytes buf.val)⟩ := by
  unfold specialized.pclmulqdq.State.update
  rcases s with ⟨k⟩
  cases k
  · exact calculate_eq st buf
  · exact calculate_avx2_eq st buf
  · exact calculate_avx512_eq st buf

theorem state_clone_eq (s : specialized.pclmulqdq.State) :
    specialized.pclmulqdq.State.Insts.CoreCloneClone.clone s = ok s := by
  rcases s with ⟨k⟩
  simp only [specialized.pclmulqdq.State.Insts.CoreCloneClone.clone,
    specialized.pclmulqdq.Kind.Insts.CoreCloneClone.clone, bind_ok]

end Crc32fastVerif
