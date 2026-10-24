# Verify Everything (agent context)

This context is loaded by the Gemini CLI extension. It is short on purpose; the skills hold the
workflows.

- Skills: `verify-library` (start here), `pick-verification-target`, `lean-aeneas-proofs`,
  `framac-wp-proofs`, `cbmc-bounded-checks`, `verification-setup`, `submit-verification-results`,
  `review-verification-claim`.
- Tools come from the `vkit` command (`vkit doctor` shows what is installed). If `vkit` is
  missing, install it: `curl -fsSL https://raw.githubusercontent.com/Verify-Everything/verified-libs/main/install.sh | bash`.
- Admission rules: https://github.com/Verify-Everything/verified-libs/blob/main/STANDARDS.md.
  Only `full-correctness` on every function admits. Never weaken a claim to make it pass (no
  `sorry`, `admit`, new `axiom`, `native_decide`, `bv_decide`).
- When working inside a clone of verified-libs, follow its `AGENTS.md`.
- Ask the user before installing system packages, pushing, opening PRs or filing upstream issues.
