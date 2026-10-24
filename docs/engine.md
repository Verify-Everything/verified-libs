# vpipe: on-demand verification pipeline

Runs formal verification on pinned library versions, records results, and improves itself.

## Start in a fresh container
    bash /mnt/project-files/pipeline/bootstrap.sh        # installs tools, runs the gate (~2 min + downloads)
    export PATH="$HOME/.vpipe/bin:$PATH"

## Everyday use
    vpipe new semver --lang rust --upstream https://github.com/dtolnay/semver --commit <sha> --version 1.0.23
    vpipe run semver                 # fetch, extract, prove, write results/semver/latest.json
    vpipe run semver --agent         # same, but a Claude agent writes specs/proofs for up to 3 rounds
    vpipe run-all                    # every manifest in libraries/ (use after a tool upgrade)
    vpipe report                     # rebuild results/SUMMARY.md

## Self-update
    vpipe improve                    # agent reads notes + results + backlog, changes the pipeline,
                                     # protected gate decides keep or roll back, logged in self/CHANGELOG.md
    vpipe improve --goal "..."       # implement a specific change to the pipeline itself
    vpipe improve --propose          # write a proposal only (self/proposals/)
    vpipe upgrade-tools              # try the newest Aeneas release; kept only if the full gate passes
    vpipe rollback [snapshot]        # undo the last self-change

## Layout
    bin/vpipe.py           the pipeline (one file)
    toolchain/             pinned versions + setup scripts
    templates/             manifest and project templates, agent prompts
    libraries/<lib>.toml   one manifest per library
    libraries/<lib>/          specs and proofs (Lean project or annotated C)
    results/<lib>/         one JSON per run + latest.json; results/SUMMARY.md
    self/                  gate.py (protected), CHANGELOG.md, BACKLOG.md, snapshots/
    selftest/              protected fixtures the gate proves on every self-change
    checklists/            new-library checklist

## Safety rules of the self-update loop
- It may edit only bin/, toolchain/, templates/, checklists/, README, VERSION, bootstrap.sh and the
  self/ logs. It never touches proofs, results, manifests, the notes folder, the gate or fixtures.
- Every change is snapshotted first, then judged by self/gate.py in a fresh process. A failed gate
  restores the snapshot. Kept and rolled-back changes are both logged with reasons.
- It never pushes, opens PRs or creates repositories.

## Environment facts (this cloud setup)
- Blocked: opam.ocaml.org, release.lean-lang.org, cache.mathlib.org, api.github.com (so no nix
  github: flakes). Allowed: github.com git + release downloads, crates, cache.nixos.org.
- Mathlib therefore builds from source unless a cache tarball exists in pipeline/cache/ or
  verification-notes/cache/; vpipe restores one automatically and publishes one after a build.
- /mnt/project-files is noexec: call scripts through bash/python3 (bootstrap does this).
