import Crc32fast.SimdTailDefs

open x86

namespace Crc32Spec

/-- Tail lengths 1 to 3, kernel-checked on the 128 basis vectors (split by tail length
    so each module's kernel replay stays small). -/
theorem tail_x_basis1 : ∀ n, n < 4 → 1 ≤ n → ∀ j, j < 128 →
    R16 (tailStep n (eW 128 j) 0#128) = Zn n (R16 (eW 128 j)) := by
  decide +kernel

end Crc32Spec
