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

## Admission standard (verified-libs)
Every run checks the ten gates of the approved standard and writes the entry's CLAIM.md
(front matter + claim card). Only `vpipe admit` moves an entry from candidates/ to libs/, and only
when every gate passes.

    vpipe new mylib --lang rust ... --version 1.2.3   # creates candidates/mylib/1.2.3/{vpipe.toml,proof/,spec/,pipeline/run.sh}
    vpipe run mylib/1.2.3 --clean    # proves from scratch; two matching clean runs = gate 9
    vpipe card mylib                 # re-check gates after editing functions.toml / [scope] / [review]
    vpipe mutate mylib --suggest 20  # candidate planted bugs; the reviewer writes mutants.toml
    vpipe mutate mylib               # runs mutants.toml; every mutant must break a proof (gate 6)
    vpipe check-upstream             # newer upstream releases are recorded as stale (not verified)
    vpipe admit mylib/1.2.3          # candidates/ -> libs/ when all ten gates pass
    vpipe export mylib --dest ~/verified-libs   # copy the entry into a verified-libs clone
    vpipe next neovim / vpipe take neovim src/x.c:f --by <session>   # work queue for big libraries

Per-function labels (full-correctness, safety-contracts, no-ub, bounded, tested) come from
`label = ...` in functions.toml, capped by the evidence: CBMC harnesses (`verified_by = "cbmc"`,
`harness = "cbmc ... --unwinding-assertions"`) are always `bounded`; a C function without an
`ensures` contract is at most `no-ub`. The entry's strength is its weakest function.
Lean entries are also replayed through the kernel with `leanchecker`. Known tool soundness bugs go
in toolchain/soundness.toml (protected); affected entries become broken.

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
    candidates/<name>/<version>/   entries not yet admitted: vpipe.toml, CLAIM.md, proof/, spec/, pipeline/run.sh
    libs/<name>/<version>/         admitted entries (same layout)
    libraries/<lib>/       older one-folder layout, still read (vpipe export moves or copies it)
    results/<entry>/       one JSON per run + latest.json, mutants.json, upstream.json; results/SUMMARY.md
    self/                  gate.py (protected), CHANGELOG.md, BACKLOG.md, snapshots/
    selftest/              protected fixtures the gate proves on every self-change
    checklists/            new-library checklist

## Safety rules of the self-update loop
- It may edit only bin/, toolchain/, templates/, checklists/, README, VERSION, bootstrap.sh and the
  self/ logs. It never touches proofs, results, manifests, libs/, candidates/, the gate, its fixtures or
  toolchain/soundness.toml.
- Every change is snapshotted first, then judged by self/gate.py in a fresh process. A failed gate
  restores the snapshot. Kept and rolled-back changes are both logged with reasons.
- It never pushes, opens PRs or creates repositories.

## Environment facts (this cloud setup)
- Blocked: opam.ocaml.org, release.lean-lang.org, cache.mathlib.org, api.github.com (so no nix
  github: flakes). Allowed: github.com git + release downloads, crates, cache.nixos.org.
- Mathlib therefore builds from source unless a cache tarball exists in pipeline/cache/ or
  verification-notes/cache/; vpipe restores one automatically and publishes one after a build.
- /mnt/project-files is noexec: call scripts through bash/python3 (bootstrap does this).
