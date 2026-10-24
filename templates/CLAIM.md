---
library: example-lib            # upstream name
version: 1.2.3                  # exact version verified (matches the folder name)
source: https://example.com/example-lib
commit: 0000000000000000000000000000000000000000   # full upstream commit
archive_sha256: <sha-256 of the upstream source archive>
tool: Lean 4 + Aeneas           # verifier(s) used
tool_version: <versions, or container digest>
strength: full-correctness      # weakest function: full-correctness | safety-contracts | no-ub | bounded | tested
status: candidate               # candidate | verified | stale | broken | revoked
functions: 0/0                  # functions at full-correctness / all functions
---

# <library> <version>: CLAIM

<!-- Claim card (format from the verified-libs admission standards). Reviewers and users read
     this, not the proofs. Write "Success criteria" and "Specification: plain words" FIRST and get
     them reviewed before any proof work. The pipeline fills generated fields from each run. -->

<!-- status, strength and functions live in the front matter above; CI reads them. -->

## Success criteria (written before proof work)
- Written: <date>. Reviewed by: <maintainer, not the author>, <date, PR/comment link>
- Every function in the pinned source (all features, all supported targets, trait impls) reaches
  full-correctness for all inputs.
- Library-specific properties:
  - <e.g. decode(encode(x)) = x for every byte string x>
  - <e.g. output equals RFC 3986 section 2.1 for every input>

## Code
- Upstream: <repo URL> @ <40-hex commit>, archive SHA-256 <hash>
- Fork (if any): <repo URL> @ <commit>; fixes listed below
- Features and targets covered: <all, listed>

## Specification
- Plain words: <what the library promises>
- Formal spec files: <paths>
- Matches standard / test vectors: <RFC, vectors used>

## Proof
- Tool(s) and versions: <tool, version, container digest>
- Per-function results: functions.toml (label + theorem for each function)
- Planted-bug check: <n (at least 10, chosen by the reviewer)> mutants, all rejected
- Differential cross-check of the translation: <cases, result>

## Trusted base
- Axioms reported by the checker: <list; only propext, Classical.choice, Quot.sound plus listed models>
- Std or library models: <each, with its differential test>
- Tool assumptions: <translator faithful, memory model, etc.>
- Unsafe / FFI boundaries: <each, and how it is proved>

## Not covered
- <must be empty for status verified>

## Bounds (only for `bounded`)
- <loop unwinding, input sizes; such entries stay under candidates/>

## How to re-check
```bash
./pipeline/run.sh
```

## Bugs found and fixes
- <bug, severity, proved fix, upstream issue link>

## Credits
- <who did the work, as they wish to be credited>

## Review
- Maintainer sign-off: <name, date>
- Adversarial review: <session/report link, date>
- Last clean CI re-check: <date, run link>
