import Lake
open Lake DSL
-- Rendered by vpipe with the Aeneas commit pinned in toolchain/versions.toml.
require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @ "fdebf20d78e8007bb92fc17068f17fc2e6cfbbbf" / "backends/lean"
package «crc32fast»
@[default_target] lean_lib «Crc32fast» where
  globs := #[.submodules `Crc32fast]
