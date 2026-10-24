# Adding a library

The `verify-library` skill walks an agent through these same steps.

**Finished means every function.** A library is done only when every function in the pinned
upstream source is verified or has a verified fix (`Functions N/N`). Unsupported or
cfg-excluded functions stay open until handled (patch, model crate, verified fix, other tool).

## 1. Fit
Widely used, small to medium (under ~5k lines in the part you verify), no public verification
attempt. Record the prior-work search in the manifest comment. Open a "Submit a library" issue
to claim it.

## 1b. Claim card and success criteria
`vkit new` (step 3) writes `libraries/<lib>/CLAIM.md`. Fill "Success criteria" and
"Specification: plain words", then open a draft PR with only the manifest and the card. The
maintainer approves them before you write any spec or proof. Read [STANDARDS.md](../STANDARDS.md)
first: only full-correctness on every function, feature and target of the real code admits;
everything else is a candidate.

## 2. Tool
Rust: Lean via Aeneas. C: CBMC first, then Frama-C WP. Other languages: open an issue to add a
tool template first.

## 3. Pin and scaffold
```bash
vkit new <lib> --lang rust|c --upstream <git url> --commit <full sha> --version <tag>
```
Creates `libraries/<lib>/` with `vpipe.toml` and the proof project.

## 4. Extract first, spec later
`vkit run <lib> --extract-only` (Rust). Read the skipped/unsupported items in
`results/<lib>/latest.json` before writing any spec. Known fixes:
[skills/verify-library/references/scoping.md](../skills/verify-library/references/scoping.md).

## 5. Headline properties, then every function
`[scope].properties`: 2-5 statements users care about. `[scope].exclusions`: assumptions only
(std models, overflow bounds, tool-friendly rewrites), never skipped functions. Example from
crc32fast:
```toml
[scope]
properties = [
  "update_slow, update_fast_16 and hash equal the bit-at-a-time reference CRC-32",
  "Hasher::update then finalize equals hash of the concatenated input",
  "combine and Hasher::combine equal the CRC of the concatenation",
]
exclusions = [
  "SIMD paths (specialized::pclmulqdq, aarch64) are not extracted",
  "Hasher::update assumes the u64 byte counter does not overflow",
]
```
Then work down the `functions` list in `results/<lib>/latest.json`. Each needs a proved theorem
that specifies it (Lean) or proved WP goals plus an `ensures` contract (C). Map model-crate
theorems or record verified fixes in `libraries/<lib>/functions.toml`:
```toml
[[function]]
id = "src/lib.rs:Hasher::update"       # as listed in results/<lib>/latest.json
theorems = ["Hasher.update_spec"]
# status = "fixed"; fix = "patches/fix-overflow.patch"   # only for a verified fix
```

## 6. Prove
By hand or with `vkit run <lib> --agent`. Re-run `vkit run <lib>` until green and Functions is N/N.

## 7. Mutation check
Plant bugs in a copy of the source and confirm each breaks a proof. Do your own early; for
admission the reviewer picks at least 10 and every one must be rejected. Record results in CLAIM.md.

## 8. Notes and report
- `libraries/<lib>/NOTES.md`: status (Functions N/M), properties, assumptions, how to re-run, timings.
- Lessons for everyone: `notes/general.md`, dated heading.
- `vkit report`.

## 9. PR
Complete the rest of CLAIM.md (Code, Proof, Trusted base, Not covered, Bugs and fixes). Leave
Status `candidate` and the Review lines to the reviewers.
See [CONTRIBUTING.md](../CONTRIBUTING.md#what-a-pr-must-show). Finished examples:
`libraries/crc32fast/`, `libraries/percent-encoding/`.

## Re-checking after an upstream release
Bump `commit`/`version` in the manifest, `vkit run <lib>`. If extraction changed, the engine
writes `External/*.new` and the result shows which theorems broke. Fix, then PR.
