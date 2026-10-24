import Lake
open Lake DSL

-- Pinned to the Aeneas release whose binaries produced the extracted code.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "fdebf20d78e8007bb92fc17068f17fc2e6cfbbbf" / "backends/lean"

package «percent_encoding_verif» where

@[default_target] lean_lib PercentEncoding {}
@[default_target] lean_lib Proofs {}
-- Non-module proof files (see the header of Proofs/Sets.lean).
@[default_target] lean_lib ProofsSets where
  roots := #[`Proofs.Sets, `Proofs.Traits, `Proofs.Alloc]
