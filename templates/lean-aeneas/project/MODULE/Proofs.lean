import {{module}}.Spec
open Aeneas Aeneas.Std Result

/-! Proofs that the extracted code (namespace from Aeneas) matches {{module}}.Spec.
Pattern that works: `theorem f_spec ... : ∃ r, f x = ok r ∧ P r := by unfold f; progress*`
then close arithmetic side goals with `simp_all`, `omega`, `scalar_tac`. -/
