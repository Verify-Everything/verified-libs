import Demo.Extracted.Funs
open Aeneas Aeneas.Std Result

namespace demo

/-- add_sat never fails and returns min (a + b) U32.MAX. -/
theorem add_sat_spec (a b : Std.U32) :
    add_sat a b ⦃ r => r.val = min (a.val + b.val) Std.U32.max ⦄ := by
  have ha := a.hmax
  have hb := b.hmax
  unfold add_sat
  step* <;> simp_all [core.num.U32.MAX, U32.max, U32.rMax, U32.numBits] <;> omega

end demo
