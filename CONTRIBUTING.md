# Contributing to verified-libs

Thanks for wanting to add receipts.

## Submitting a library

1. **Open an issue** with the *Submit a library* form. Name the library and version, the tool, the target strength level, and the success criteria (what will count as done). This lets others weigh in before you invest the effort.
2. **Create the entry** at `libs/<library>/<version>/`:
   - `CLAIM.md`: copy [`templates/CLAIM.md`](templates/CLAIM.md) and fill in every field.
   - `spec/`: the formal specification.
   - `proof/`: proofs or verification harnesses.
   - `pipeline/run.sh`: re-checks everything from a clean checkout and exits `0` only on success. Pin the toolchain, ideally with `pipeline/Dockerfile`.
3. **Run the structure check** locally:
   ```bash
   python scripts/check_structure.py
   ```
4. **Open a PR** and complete the checklist in the template.

## Reviews

A reviewer will:

- re-run `pipeline/run.sh`;
- read the claim card against the specs, and challenge anything it overstates;
- make sure the **Not covered** and **Trusted base** sections are honest and specific.

## Found an unsound or overstated claim?

That counts as a security issue for this project. Please report it privately, as described in the org's security policy, rather than in a public issue.

## Standards changes

Use the *Propose a standards change* issue form. The standards are a draft ([STANDARDS.md](STANDARDS.md)), and good arguments change them.

## Conduct

Participation is covered by the org's Code of Conduct.
