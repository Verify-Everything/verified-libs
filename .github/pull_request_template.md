## What this PR does

<!-- New entry, update to an entry, standards change, engine/toolkit change. Link the issue. -->

## For new or updated entries

- [ ] Entry is at `libs/<library>/<version>/` (admitted) or `candidates/<library>/<version>/`
- [ ] Success criteria were approved in the issue before proof work started (link):
- [ ] `CLAIM.md` is complete, including **Trusted base** and **Not covered**
- [ ] `pipeline/run.sh` re-checks everything from a clean checkout, and the toolchain is pinned
- [ ] `python3 scripts/check_structure.py` and `python3 scripts/check-repo.py` pass
- [ ] Nothing in the claim card says more than the proof does

## Claim card
<!-- libraries/<lib>/CLAIM.md must be complete. Link the PR or comment where the success criteria were approved. -->
- CLAIM.md complete: yes / no. Status requested: candidate / verified
- Success criteria approved before proof work by the maintainer: link
- Entry strength (weakest function: full-correctness / safety-contracts / no-ub / bounded / tested):
- Planted bugs (at least 10, chosen by the reviewer), all rejected: yes / no
- Two sign-offs for "verified" (author can be neither): maintainer @ ; adversarial review report: link

## Functions
<!-- From results/<lib>/latest.json. Finished only at N/N; otherwise list what is still open. -->
Functions verified or fixed: N/M

## Claims
<!-- One line per property, with its strength: proved / bounded-checked (bound) / tested. -->
-

## Assumptions
<!-- Std models, tool-friendly patches, overflow bounds. Must match the manifest's exclusions. -->
-

## Evidence
<!-- Commands you ran and what they printed. Paste the summary from results/<lib>/latest.json. -->
- `vkit run <lib>`:
- Proved / total, sorries, extra-axiom theorems, std-model axioms, skipped:
- Mutation check (mutant → caught by):
- `vkit selftest` (engine changes: `--full`):

## Upstream
<!-- Bugs found? Link the draft in libraries/<lib>/upstream-issue.md. "none" if none. -->

## Human owner
<!-- A person completes this. Agents leave it unchecked. -->
Owner: @
- [ ] I read the final diff and the spec, and I can explain what is claimed and assumed.
- [ ] The evidence above came from runs on the current diff.
