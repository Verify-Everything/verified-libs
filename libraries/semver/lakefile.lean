import Lake
open Lake DSL
-- Rendered by vpipe with the Aeneas commit pinned in toolchain/versions.toml.
require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @ "fdebf20d78e8007bb92fc17068f17fc2e6cfbbbf" / "backends/lean"
package «semver_verif» where
  leanOptions := #[⟨`weak.linter.dupNamespace, false⟩]
@[default_target] lean_lib «SemverModel»
