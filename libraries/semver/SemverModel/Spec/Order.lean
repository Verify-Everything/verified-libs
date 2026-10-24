import SemverModel.Spec.Lists
/-!
# Version precedence is a total order

The mirrors of `Ord for Prerelease`, `Ord for BuildMetadata` and
`#[derive(Ord)] for Version` are shown equal to key comparisons built from
Lean's lexicographic combinators. Lean's core library already proves those
combinators transitive and antisymmetric (`Std.TransCmp`), and we add
`Std.LawfulEqCmp` (comparing `.eq` means equal) by hand.
-/
open Aeneas Aeneas.Std Std

namespace SemverSpec

/-! ## Generic helpers -/

/-- Comparing through a function keeps transitivity. -/
theorem transCmp_pullback {α β : Type} (cmp : β → β → Ordering) [TransCmp cmp] (f : α → β) :
    TransCmp (fun a b => cmp (f a) (f b)) where
  eq_swap := OrientedCmp.eq_swap (cmp := cmp)
  isLE_trans h1 h2 := TransCmp.isLE_trans (cmp := cmp) h1 h2

/-- Comparing through an injective function keeps lawful equality. -/
theorem lawfulEqCmp_pullback {α β : Type} (cmp : β → β → Ordering) [LawfulEqCmp cmp] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) : LawfulEqCmp (fun a b => cmp (f a) (f b)) where
  compare_self := ReflCmp.compare_self (cmp := cmp)
  eq_of_compare h := hf _ _ (LawfulEqCmp.eq_of_compare (cmp := cmp) h)

/-! ## Segments -/

instance : TransCmp preSegL := by unfold preSegL; infer_instance
instance : TransCmp buildSegL := by unfold buildSegL; infer_instance

instance : LawfulEqCmp preSegL where
  compare_self := ReflCmp.compare_self (cmp := preSegL)
  eq_of_compare {a b} h := by
    simp only [preSegL, compareLex_eq_eq, compareOn] at h
    exact bytesN_inj (LawfulEqOrd.eq_of_compare h.2.2)

instance : LawfulEqCmp buildSegL where
  compare_self := ReflCmp.compare_self (cmp := buildSegL)
  eq_of_compare {a b} h := by
    simp only [buildSegL, compareLex_eq_eq, compareOn] at h
    exact bytesN_inj (LawfulEqOrd.eq_of_compare h.2.2.2.2)

/-! ## Prerelease and build metadata -/

/-- Prerelease order: the empty prerelease (a release) is greatest; otherwise
compare `.`-separated segments lexicographically. -/
def preL : List U8 → List U8 → Ordering :=
  compareLex (compareOn fun l => if l = [] then 1 else 0)
    (fun a b => List.compareLex preSegL (splitDot a) (splitDot b))

/-- Build metadata order: compare `.`-separated segments lexicographically. -/
def buildL : List U8 → List U8 → Ordering :=
  fun a b => List.compareLex buildSegL (splitDot a) (splitDot b)

instance : TransCmp preL := by
  unfold preL
  have := transCmp_pullback (List.compareLex preSegL) splitDot
  infer_instance

instance : TransCmp buildL := transCmp_pullback (List.compareLex buildSegL) splitDot

instance : LawfulEqCmp buildL :=
  lawfulEqCmp_pullback (List.compareLex buildSegL) splitDot (fun _ _ h => splitDot_inj h)

instance : LawfulEqCmp preL where
  compare_self := ReflCmp.compare_self (cmp := preL)
  eq_of_compare {a b} h := by
    simp only [preL, compareLex_eq_eq] at h
    exact splitDot_inj (LawfulEqCmp.eq_of_compare (cmp := List.compareLex preSegL) h.2)

theorem splitDot_nil : splitDot [] = [[]] := by
  unfold splitDot; rw [splitFrom_unfold [] 0 (Nat.le_refl _)]
  simp [sub, segEnd]

theorem preCmp_eq (l r : List U8) : preCmp l r = preL l r := by
  unfold preCmp preL
  simp only [compareLex, compareOn]
  by_cases hl : l = [] <;> by_cases hr : r = []
  · subst hl hr; simp [splitDot_nil]; rfl
  · subst hl; have : r.length ≠ 0 := by simpa using hr
    simp [this, hr]; rfl
  · subst hr; have : l.length ≠ 0 := by simpa using hl
    simp [this, hl]; rfl
  · have h1 : l.length ≠ 0 := by simpa using hl
    have h2 : r.length ≠ 0 := by simpa using hr
    simp only [h1, h2, hl, hr, ite_false]
    rw [cmpSegsLoop_eq _ _ _ _ _ _ (Nat.zero_le _) (Nat.zero_le _)]
    simp [segL, splitDot]

theorem buildCmp_eq (l r : List U8) : buildCmp l r = buildL l r := by
  unfold buildCmp buildL
  by_cases h : l.length = 0 ∧ r.length = 0
  · simp only [h, and_self, ite_true]
    have hl : l = [] := List.eq_nil_of_length_eq_zero h.1
    have hr : r = [] := List.eq_nil_of_length_eq_zero h.2
    subst hl hr; rw [splitDot_nil]; exact (ReflCmp.compare_self (cmp := List.compareLex buildSegL)).symm
  · simp only [h, ite_false]
    rw [cmpSegsLoop_eq _ _ _ _ _ _ (Nat.zero_le _) (Nat.zero_le _)]
    simp [segL, splitDot]

/-! ## Versions -/

/-- Version precedence as a key comparison: major, minor, patch, prerelease, build. -/
def versionL : PVersion → PVersion → Ordering :=
  compareLex (compareOn PVersion.major) <|
  compareLex (compareOn PVersion.minor) <|
  compareLex (compareOn PVersion.patch) <|
  compareLex (fun a b => preL a.pre b.pre) (fun a b => buildL a.build b.build)

theorem versionCmp_eq (a b : PVersion) : versionCmp a b = versionL a b := by
  unfold versionCmp versionL
  simp only [compareLex, compareOn, cmpNat_eq, preCmp_eq, buildCmp_eq]
  cases compare a.major b.major <;> try rfl

instance : TransCmp versionL := by
  unfold versionL
  have := transCmp_pullback preL PVersion.pre
  have := transCmp_pullback buildL PVersion.build
  infer_instance

instance : LawfulEqCmp versionL where
  compare_self := ReflCmp.compare_self (cmp := versionL)
  eq_of_compare {a b} h := by
    simp only [versionL, compareLex_eq_eq, compareOn] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have := LawfulEqOrd.eq_of_compare h1
    have := LawfulEqOrd.eq_of_compare h2
    have := LawfulEqOrd.eq_of_compare h3
    have := LawfulEqCmp.eq_of_compare (cmp := preL) h4
    have := LawfulEqCmp.eq_of_compare (cmp := buildL) h5
    cases a; cases b; simp_all

/-- The mirror of semver's `Ord for Version` is a lawful total order. -/
instance : TransCmp versionCmp := by
  have : versionCmp = versionL := by funext a b; exact versionCmp_eq a b
  rw [this]; infer_instance

instance : LawfulEqCmp versionCmp := by
  have : versionCmp = versionL := by funext a b; exact versionCmp_eq a b
  rw [this]; infer_instance

end SemverSpec
