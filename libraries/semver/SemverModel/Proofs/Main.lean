import SemverModel.Proofs.RoundTrip
import SemverModel.Proofs.Order
/-!
# Headline theorems about the extracted Rust code

All statements are about the Aeneas translation of `model/src/lib.rs`.
-/
open Aeneas Aeneas.Std Result
open semver_model SemverSpec

namespace SemverProofs

/-- `parse_version` never panics or overflows: it always returns a `Result`. -/
theorem parse_version_total (s : Slice U8) : ∃ r, parse_version s = ok r := by
  obtain ⟨r, hr, _⟩ := spec_exists (parse_version_spec s); exact ⟨r, hr⟩

/-- Parse then print: if `parse_version` accepts some bytes, `version_to_bytes`
gives back exactly those bytes. -/
theorem parse_then_print (s : Slice U8) (v : Version) (h : parse_version s = ok (.Ok v)) :
    ∃ b, version_to_bytes v = ok b ∧ b.val = s.val := by
  have hp := parse_version_spec s
  rw [h] at hp
  simp only [WP.spec_ok, resMap_ok] at hp
  have hprint := parse_print s.val v.toP hp.symm
  have hlen : (printM v.toP).length ≤ Usize.max := by rw [hprint]; exact Slice.length_ineq s
  obtain ⟨b, hb, hbv⟩ := spec_exists (version_to_bytes_spec v hlen)
  exact ⟨b, hb, by rw [hbv, hprint]⟩

/-- Print then parse: a version whose prerelease and build parts are each
accepted on their own (as `Prerelease::new` / `BuildMetadata::new` would) and
whose text fits in memory prints to bytes that `parse_version` reads back as
the same version. -/
theorem print_then_parse (v : Version)
    (hpre : identWholeM v.pre.ident.val true = .Ok v.pre.ident.val)
    (hbuild : identWholeM v.build.ident.val false = .Ok v.build.ident.val)
    (hlen : (printM v.toP).length ≤ Usize.max) :
    ∃ b, version_to_bytes v = ok b ∧ parse_version (alloc.vec.Vec.deref b) = ok (.Ok v) := by
  obtain ⟨b, hb, hbv⟩ := spec_exists (version_to_bytes_spec v hlen)
  refine ⟨b, hb, ?_⟩
  obtain ⟨r, hr, hp⟩ := spec_exists (parse_version_spec (alloc.vec.Vec.deref b))
  rw [hr]
  have hpp := print_parse v.toP (by simp [Version.toP]; scalar_tac) (by simp [Version.toP]; scalar_tac)
    (by simp [Version.toP]; scalar_tac) hpre hbuild
  rw [deref_val, hbv, hpp] at hp
  cases r with
  | Ok w => simp only [resMap_ok, core.result.Result.Ok.injEq] at hp; rw [toP_inj w v hp]
  | Err e => simp at hp

/-- The accepted-on-its-own condition is exactly what `parse_prerelease` checks. -/
theorem parse_prerelease_accepts (s : Slice U8) (p : Prerelease)
    (h : parse_prerelease s = ok (.Ok p)) : identWholeM p.ident.val true = .Ok p.ident.val := by
  have hp := parse_prerelease_spec s
  rw [h] at hp
  simp only [WP.spec_ok, resMap_ok] at hp
  have := hp.symm
  unfold identWholeM at this ⊢
  split at this
  · simp at this
  · rename_i e he
    split_ifs at this with h1
    simp only [core.result.Result.Ok.injEq] at this
    subst h1
    have hlen := (sub_length s.val 0 s.val.length (Nat.le_refl _))
    rw [sub_zero_full] at this
    rw [← this, he]; simp [sub_zero_full]

theorem parse_build_accepts (s : Slice U8) (p : BuildMetadata)
    (h : parse_build s = ok (.Ok p)) : identWholeM p.ident.val false = .Ok p.ident.val := by
  have hp := parse_build_spec s
  rw [h] at hp
  simp only [WP.spec_ok, resMap_ok] at hp
  have := hp.symm
  unfold identWholeM at this ⊢
  split at this
  · simp at this
  · rename_i e he
    split_ifs at this with h1
    simp only [core.result.Result.Ok.injEq] at this
    subst h1
    rw [sub_zero_full] at this
    rw [← this, he]; simp [sub_zero_full]

end SemverProofs
