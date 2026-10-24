# Standards

> **Status: approved by the maintainer, 2026-10-24.** Propose changes with the *Propose a standards
> change* issue form; a change needs the maintainer's approval.

## What "verified" means
The exact upstream source at a pinned commit (or a published fork with proved fixes) is proved,
by a recorded tool, to meet a formal specification for all inputs, with every assumption
listed. It does not mean built from source, scanned, fuzzed or tested. Anything weaker can be
published under `candidates/`, never with the word "verified".

## Threat model
Attackers who use AI to find bugs at scale, and contributors who may be careless, automated or
hostile. So we assume someone will look for: inputs the proof did not cover (sizes, features,
targets, model-vs-code gaps); proofs that pass by weakening the spec, adding an axiom or using a
checker shortcut; tampering with the repo, toolchain or upstream source; and soundness bugs in
the tools.

## The ten gates (all required, no waivers)
1. **The real code.** Upstream at a pinned commit, byte for byte, or a published fork whose only
   changes are fixes with their own proofs. A patch made only so a tool can read the code must be
   proved equivalent to the original.
2. **Every function.** All public API, everything it reaches, trait impls (Display, Debug,
   derived), every Cargo feature or build option, every supported target (SIMD paths included).
3. **All inputs.** No bounded checks, no size caps.
4. **Full strength.** Every function at `full-correctness`.
5. **Specification first.** Spec and success criteria written and reviewed before proof work; no
   changes afterwards without a new review.
6. **Not vacuous.** Spec matches published test vectors or the governing standard; at least 10
   planted bugs, chosen by the reviewer, each make the proof fail.
7. **Clean trusted base.** No forbidden constructs; every remaining assumption named in CLAIM.md
   and checked against the checker's own axiom report.
8. **Independent cross-check.** The tool's translation is differential-tested against the
   compiled upstream library.
9. **Reproducible from scratch.** CI rebuilds and re-checks from clean, in a container pinned by
   digest, no cached proof results, same result on two runs.
10. **Two reviews.** A human maintainer and a fresh adversarial review agent (no access to the
    prover's notes). The author can't be either.

## Strength labels (one per function; the entry takes the weakest)
| Label | Meaning | Admits |
|---|---|---|
| `full-correctness` | meets a functional spec for all inputs; no UB, panic or crash on any accepted input | yes |
| `safety-contracts` | proved memory/bounds pre/postconditions, not full behaviour | no |
| `no-ub` | proved free of undefined behaviour only | no |
| `bounded` | checked up to a size or loop bound (CBMC, Kani, size caps) | no |
| `tested` | differential or property tests only | no |

## Model crates and unsafe code
Proofs about a hand-written model don't count unless the entry also proves model-to-code
equivalence, or the model replaces the real code in a published fork users can adopt. Code one
tool can't read (`unsafe`, FFI) gets a second tool (Verus, unbounded Kani, Frama-C, VeriFast)
with the proofs linked.

## Forbidden constructs (CI fails the entry)
| Tool | Forbidden | Allowed only if listed in CLAIM.md |
|---|---|---|
| Lean / Aeneas | `sorry`, `admit`, new `axiom`s, `native_decide`, `bv_decide`, `implemented_by`, `@[extern]`, `unsafe`, `opaque` in specs, options that skip kernel checks; `#print axioms` beyond propext, Classical.choice, Quot.sound and listed models | std models in FunsExternal, each differential-tested against real std |
| Frama-C / WP | `admit` clauses, unproved goals, runs without `-wp-rte`, unchecked `assumes` | lemmas proved separately by another prover, proof in the repo |
| CBMC / Kani | runs without unwinding assertions | bounded results, under `candidates/` only |
| Any | model-crate proofs without a model-to-code proof; edits to the pinned source | fix patches with their own proofs |
Lean proofs are also replayed by `lean4checker`.

## Supply chain
Upstream pinned by commit and archive SHA-256; toolchains by container digest. Signed commits and
tags on main; no direct or force pushes; two sign-offs to merge. PR CI runs without secrets.
Release artifacts carry GitHub artifact attestations. Tool soundness bugs trigger a re-check of
every entry using that tool.

## Lifecycle
| Event | Status |
|---|---|
| weekly clean re-check fails, or no green run in 14 days | `broken` (badge removed within 24 h) |
| upstream releases a new version | new version is `stale`/candidate; old stays verified |
| soundness bug announced in a tool used | `broken` until re-checked on a fixed version |
| spec found wrong or too weak | `revoked`, public notice, full re-review to return |
| bug found in verified code | `revoked`, handled as a security incident (notify upstream privately first) |

## Layout
```
libs/<library>/<version>/{CLAIM.md, spec/, proof/, pipeline/}      admitted entries (status verified, stale, broken, revoked)
candidates/<library>/<version>/{...same...}                       everything below full-correctness, never called verified
```
Library and version folder names use lowercase letters, digits, `.`, `_` and `-`. Until the vpipe
engine reads these folders, work in progress lives in the engine's `libraries/<lib>/` (all
current entries there are candidates).

## What CI enforces today
- `scripts/check_structure.py`: layout, CLAIM.md front matter, labels and statuses; only
  `full-correctness` with both sign-offs under `libs/`; "Not covered" empty for `verified`.
- `scripts/check-repo.py`: CLAIM.md present with the required sections; forbidden Lean constructs
  in hand-written proof files; "verified" status with placeholders or a non-empty "Not covered".
- Engine: every-function inventory (Functions N/M) and the Lean axiom audit.
- Not yet automated (tracked for the engine): lean4checker replay, container digests, archive
  SHA-256, two-run reproducibility, FunsExternal model tests. Until automated, reviewers check them.
