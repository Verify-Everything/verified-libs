import Crc32fast.SimdTailDefs

open x86

namespace Crc32Spec

/-- Tail lengths 4 to 7, kernel-checked on the 128 basis vectors (split by tail length
    so each module's kernel replay stays small). -/
theorem tail_p_basis2 : ∀ n, n < 8 → 4 ≤ n → ∀ j, j < 128 →
    R16 (tailStep n 0#128 (eW 128 j)) = Rn (eW 128 j) n := by
  decide +kernel

end Crc32Spec
