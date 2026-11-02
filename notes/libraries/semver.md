# semver verification status

Thread: "Verify semver in Lean". Rewritten 2026-10-24 after Yerin chose "Publish a proved fork" (07:04).
Upstream: github.com/dtolnay/semver @ 280ebcb6edac3aa4cdc545dbff8a26c5ac4861fe (1.0.28 + 3 commits).
Fork: same public API; unsafe Identifier packing replaced by safe code; every function written so Aeneas reads it
(`#![forbid(unsafe_code)]`). Published 2026-10-24 10:18 at github.com/Verify-Everything/semver, main = 28e87c4 (code + proofs/).
Stack: Aeneas nightly-2026.10.23-fdebf20 (Charon 0.1.293), Lean v4.35.0, mathlib v4.35.0.

## Proved on the fork's real code (standard axioms only, no sorry; kernel replay passes)
- Version total order; parse never panics; parse->print byte-exact; print->parse.
- Every parser (Version, VersionReq, Comparator, Prerelease, BuildMetadata) equals its spec, exact ErrorKinds.
- matches for every op incl. prerelease rules; cmp_precedence; Ord/PartialOrd/Eq/PartialEq/Hash/Clone/Default impls.
- Display/Debug of every type: the exact formatter calls (fill, width, align, {:#?}); error messages. write_str and u64 Debug are opaque std models (tools/fmt_models.py, 2026-10-26): the Aeneas library ones ignored the text, which made 19 results vacuous.
- Every parse error offset is a UTF-8 char start (so printing an error never fails); parsed identifiers are ASCII,
  which discharges the UTF-8 hypotheses of as_str/Display/Hash.
- FromStr/parse/new wrappers; serde visit_str logic (moved into api.rs); Error::new.
- Function ledger (lean/tools/Ledger.lean): all 305 extracted Lean defs are named by a proved theorem.
- Non-vacuity (2026-10-26 rule): lean/SemverModel/Api/NonVacuity.lean gives each theorem with hypotheses that no
  other proof uses a concrete instance meeting all of them, plus one concrete consequence (e.g. "1.2.3" parses and
  prints back; "x" fails with a printable error; [255] is not UTF-8; ^1.2.3, ~1.2.3, >=, <= match 1.2.3).
  lean/tools/Conditional.lean lists any left over; it now lists none. The upstream Identifier hand model
  (unsafe-code model, not the fork) was dropped from the build and archived in ~/work/semver-verif/archive/.
- Local fork commits not yet pushed (waiting on Yerin): 7de0e84 (formatter models), 0987dbd (non-vacuity). Both
  touch proofs/ only.

## Open (every-function rule) and trust
- serde.rs: 13 one-line adapters into serde (Aeneas rejects serde's mutually recursive traits), plus the
  DeError trait declaration. Differential-tested only.
- printing::push_debug_non_ascii: std char Debug (Unicode tables), opaque std model `charDebugSeg`.
- Std models listed in vpipe.toml [trust].models (Formatter state, Hash of u64/isize/str/Option/Vec).
- Gate 1 for forks: Yerin decided 10:13 the fork is the verified code. functions.toml marks the 149 rewritten functions `rewrite = "28e87c4..."` (vpipe 0.2.16), so gate 1 now fails only on the 15 open functions.
- Removed upstream functions (vpipe 0.2.30/0.2.31): functions.toml maps 67 of 80 with replaced_by (fork ids, or
  {lean, theorems} for derived Clone/PartialEq/Default and EMPTY). QuotedChar::fmt waits on push_debug_non_ascii.
  12 left: Identifier's packed-pointer helpers, ptr_eq and Drop; nothing in the fork does their job (Vec<u8>).
  The pipeline thread is asking Yerin how gate 1 should treat them (2026-10-26).
- Admission gates still missing: reviewer-chosen planted bugs (>=10), [scope].reviewed_by, two reviews,
  pinned container (gate 9).

## Files
- Work repos: ~/work/semver-verif (proofs, git), ~/work/semver-fork (fork, git). Snapshots in
  /mnt/project-files/semver-verif/ and /mnt/project-files/semver-fork/; fork git bundle
  /mnt/project-files/semver-verif/semver-fork.bundle (old; the pipeline now reads GitHub).
- Pipeline entry: pipeline/libraries/semver (fork manifest, functions.toml). Old model-crate entry backed up
  in /mnt/project-files/semver-verif/pipeline-entry-model-v1/.
