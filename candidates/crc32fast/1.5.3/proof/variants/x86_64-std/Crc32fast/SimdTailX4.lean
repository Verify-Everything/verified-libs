import Crc32fast.SimdTailDefs

open x86

namespace Crc32Spec

/-- Tail lengths 12 to 15, kernel-checked on the 128 basis vectors (split by tail length
    so each module's kernel replay stays small). -/
theorem tail_x_basis4 : ∀ n, n < 16 → 12 ≤ n → ∀ j, j < 128 →
    R16 (tailStep n (eW 128 j) 0#128) = Zn n (R16 (eW 128 j)) := by
  decide +kernel

end Crc32Spec
