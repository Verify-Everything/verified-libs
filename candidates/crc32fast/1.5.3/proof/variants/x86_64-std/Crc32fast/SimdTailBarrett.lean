import Crc32fast.SimdTailDefs

open x86

namespace Crc32Spec

/-- Kernel-checked on the 128 basis vectors. -/
theorem barrett_basis : ∀ j, j < 128 → barrett (eW 128 j) = R16 (eW 128 j) := by
  decide +kernel

end Crc32Spec
