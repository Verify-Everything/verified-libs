# Standards (draft)

> **Status: draft, open for review.** Propose changes with the *Propose a standards change* issue form. Nothing here is final until the first entry lands.

## 1. What "verified" means

An entry is verified when a machine checker accepts a proof (or exhaustive verification harnesses) that the library meets a **stated formal specification**. Supply-chain attestation, testing and fuzzing are valuable, but they are not verification in this sense.

## 2. The claim card

Every entry has a `CLAIM.md`, based on [`templates/CLAIM.md`](templates/CLAIM.md). Its front matter is machine-checked by CI; its body is written for humans. It must state:

- **Library and exact version or commit** that was verified.
- **Source**: where the library lives upstream.
- **Properties proven**, both in plain words and by pointing to the formal specs in `spec/`.
- **Tool and tool version** used to check the proof.
- **Strength level** (section 3).
- **Trusted base**: axioms, assumptions, unverified dependencies, `unsafe`/FFI boundaries, models of the environment, and the checker itself.
- **Not covered**: what the proof does not say. This section is mandatory, and "nothing" is not an acceptable answer.

## 3. Strength levels

| Level | Meaning |
|---|---|
| `functional` | Full functional correctness against a complete specification. |
| `contracts` | Pre/postconditions proven for the public API. |
| `safety` | Absence of undefined behaviour / runtime errors, unbounded. |
| `bounded` | Correct up to stated bounds (bounded model checking, bounded proofs). The bounds must be listed. |

An entry may mix levels across modules. If it does, the claim card lists the level for each part, and the headline level is the weakest one.

## 4. Re-checking pipeline

- `pipeline/run.sh` re-checks every proof from a clean checkout and exits `0` only on success.
- The toolchain is pinned, preferably with `pipeline/Dockerfile` or a lockfile, so the result is reproducible.
- If an entry's pipeline fails, the entry is marked `status: broken` rather than silently kept.

## 5. Success criteria up front

Before verification work starts, the submission issue states what counts as done: which properties, at which level, and for which version. Reviewers check the entry against those criteria.

## 6. Any tool, recorded

Any verifier is welcome (e.g. Lean, Rocq, Isabelle, Dafny, F\*, Verus, Kani, VeriFast, Why3, Frama-C, CBMC). Always record which one, with its version.

## 7. Staleness

A claim covers only the version it names. When upstream releases a new version, the entry stays valid for the old version only, until someone re-verifies it.

## 8. Layout

```
libs/<library>/<version>/{CLAIM.md, spec/, proof/, pipeline/}
```

Library and version folder names use lowercase letters, digits, `.`, `_` and `-`.

## Open questions

- Which strength levels qualify for inclusion at all?
- Who reviews a claim card before merge, and how many reviewers are required?
- Do we accept proofs about a *model* of the code, or only about the code itself? (If models are accepted, the claim card must say so in the trusted base.)
