# semver verification status

Thread: "Verify semver in Lean". Upstream: github.com/dtolnay/semver @ 280ebcb6edac3aa4cdc545dbff8a26c5ac4861fe (1.0.28 + 3 commits).
Stack: Aeneas release nightly-2026.10.23-fdebf20 (Charon 0.1.293), Rust nightly-2026-09-17, Lean v4.35.0, mathlib v4.35.0 (shared cache tarball in cache/).
Rule from Yerin (2026-10-24 05:38): not finished until every function is verified or has a verified fix.

## Approach
- `Identifier` uses unsafe pointer packing, so Aeneas can't translate upstream as is. A safe model crate (`model/`) mirrors upstream's Version code function by function, with `Identifier` replaced by `Vec<u8>` and `&str` by `&[u8]` + index ranges. Error kinds drop the offending char.
- `model/tests/differential.rs` checks model vs upstream (path dependency on the pinned checkout): parse results, printed form, and cmp for Version/Prerelease/BuildMetadata. 160k versions, 660k comparisons, all agree.
- Charon + Aeneas extract the model with no external stubs.
- Proof layers: pure Lean mirrors of each Rust function (Spec/Mirror, Spec/ParseMirror) -> refinement `fn ⦃ r => r = mirror ⦄` for every extracted function (Proofs/Refine*) -> properties on the mirrors (Spec/Order, Proofs/RoundTrip) -> headline theorems on extracted code (Proofs/Main).
- Pipeline: registered as `vpipe run semver` (pipeline/libraries/semver). The model ships as rust/model.patch on the pinned checkout; the differential test runs as the [test] step.
- Local work copy: /mnt/project-files/semver-verif/ (git repo snapshot).

## Proven (2026-10-24 ~06:00 UTC), standard axioms only, no sorry
- `version_cmp_total_order`: version_cmp = versionOrd, which is Std.TransCmp + Std.LawfulEqCmp.
- `parse_version_total`: parse_version never panics.
- `parse_then_print`: parse_version s = Ok v -> version_to_bytes v = s byte for byte.
- `print_then_parse`: v with prerelease/build each accepted alone and text ≤ usize::MAX -> parse_version (version_to_bytes v) = Ok v.
- `parse_prerelease_accepts` / `parse_build_accepts`: link the "accepted alone" condition to Prerelease::new / BuildMetadata::new.

## Still open (Yerin's every-function rule)
- Identifier unsafe packing (identifier.rs): needs a hand model of the encoding or a verified safe replacement.
- VersionReq / Comparator parsing and matching (parse.rs, eval.rs).
- Display / Debug / error messages (display.rs, error.rs), remaining trait impls (impls.rs), serde (serde.rs).
- The link model <-> upstream is a differential test, not a proof.
