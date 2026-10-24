import SemverModel.Proofs.RefineCmp
import SemverModel.Spec.Order
/-!
# Main theorem: the extracted `version_cmp` is a lawful total order

`version_cmp` (Aeneas output for the model's `Ord for Version`) never fails,
and the ordering it returns is transitive, antisymmetric (`Std.TransCmp`),
and returns `.eq` exactly on equal versions (`Std.LawfulEqCmp`).
-/
open Aeneas Aeneas.Std Result Std
open semver_model SemverSpec

namespace SemverProofs

theorem eq_ok_of_spec {α : Type} {x : Result α} {v : α} (h : x ⦃ r => r = v ⦄) : x = ok v := by
  cases x <;> simp_all [WP.spec_ok]

theorem version_cmp_ok (a b : Version) : version_cmp a b = ok (versionCmp a.toP b.toP) :=
  eq_ok_of_spec (version_cmp_spec a b)

theorem prerelease_cmp_ok (a b : Prerelease) : prerelease_cmp a b = ok (preL a.ident.val b.ident.val) := by
  rw [eq_ok_of_spec (prerelease_cmp_spec a b), preCmp_eq]

theorem build_cmp_ok (a b : BuildMetadata) : build_cmp a b = ok (buildL a.ident.val b.ident.val) := by
  rw [eq_ok_of_spec (build_cmp_spec a b), buildCmp_eq]

/-- The ordering computed by the extracted code. -/
def versionOrd (a b : Version) : Ordering := versionCmp a.toP b.toP

theorem version_cmp_eq_versionOrd (a b : Version) : version_cmp a b = ok (versionOrd a b) :=
  version_cmp_ok a b

theorem toP_inj (a b : Version) (h : a.toP = b.toP) : a = b := by
  obtain ⟨am, an, ap, ⟨apre⟩, ⟨ab⟩⟩ := a
  obtain ⟨bm, bn, bp, ⟨bpre⟩, ⟨bb⟩⟩ := b
  simp only [Version.toP, PVersion.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have := UScalar.eq_of_val_eq h1
  have := UScalar.eq_of_val_eq h2
  have := UScalar.eq_of_val_eq h3
  have := alloc.vec.Vec.ext _ _ h4
  have := alloc.vec.Vec.ext _ _ h5
  subst_vars; rfl

instance : TransCmp versionOrd := transCmp_pullback versionCmp Version.toP

instance : LawfulEqCmp versionOrd := lawfulEqCmp_pullback versionCmp Version.toP toP_inj

/-- Headline: comparing versions with the extracted code never fails and is a
lawful total order (reflexive, antisymmetric, transitive, total, and `.eq` only
for identical versions). -/
theorem version_cmp_total_order :
    (∀ a b, version_cmp a b = ok (versionOrd a b)) ∧ TransCmp versionOrd ∧ LawfulEqCmp versionOrd :=
  ⟨version_cmp_eq_versionOrd, inferInstance, inferInstance⟩

end SemverProofs
