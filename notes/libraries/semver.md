# semver verification status

Thread: "Verify semver in Lean". Upstream: github.com/dtolnay/semver @ 280ebcb6edac3aa4cdc545dbff8a26c5ac4861fe (1.0.28 + 3 commits).
Stack: Aeneas nightly-2026.10.23-fdebf20 (Charon 0.1.293), Rust nightly-2026-09-17, Lean v4.35.0, mathlib v4.35.0 (shared cache tarball).
Rules: not finished until every function is verified or has a verified fix (Yerin, 05:38). Admission standards approved 06:51: only full functional correctness on the REAL code counts.

## Status under the admission standards: CANDIDATE
Everything below is proved on a safe model crate (`model/`), not on dtolnay's code. The model is checked
against upstream only by differential tests, which the standards do not accept as a link. Decision asked of
Yerin (07:0x): link to upstream (recommended), publish a proved fork, or keep as candidate.

## Proved on the model (standard axioms only, no sorry; 25 headline theorems in lean/Check.lean)
- Version: total order (TransCmp + LawfulEqCmp), parse never panics, parse->print byte-exact, print->parse.
- eval.rs: matches_* for every op, cmp_precedence, pre_is_compatible, VersionReq::matches; properties (exact,
  >, <, >=, <=, tilde, caret ranges for full comparators; req = all comparators).
- parse.rs requirements: skip_spaces, wildcard, op, comparator parts/suffix, comparator, the version_req loop
  (32-comparator limit, wildcard errors), parse_version_req, parse_comparator. Exact upstream ErrorKinds.
- Differential tests (model vs upstream): 300k eval cases; 150k requirement strings incl. error Display/Debug,
  comparator/req Display, Version padded Display, Debug, serde_json.

## Upstream extraction test (07:05)
Charon + Aeneas on upstream as is (with `--exclude core::str::pattern`): 212 defs come out, but
- 78 std functions become axioms, including raw-pointer ops (ptr::read/write, alloc, from_raw_parts,
  transmute) used by Identifier. Axioms about raw pointers mean nothing in Aeneas's pure model, so Identifier
  needs a second tool (Kani/Verus/VeriFast) whose result is linked as a spec.
- &str ops (split, strip_prefix, trim_start_matches, bytes, split_at, ...) become axioms: allowed only if
  listed in CLAIM.md and differential-tested; better to prove Lean models of them.
- display::pad fails ("returns inside nested loops") -> needs a readability patch proved equivalent.

## Still open (every-function rule)
- Link to upstream (whichever option Yerin picks). Identifier unsafe packing is the hard part.
- Lean proofs for printing (Display/Debug/padding), error messages, serde wrappers, Hash, remaining impls.
- Requirement round trip (print->parse) and validity properties.
- Planted-bug check (>=10 mutants), CLAIM.md, pipeline functions.toml for all 92 upstream ids, model.patch refresh.

## Files
Work repo: ~/work/semver-verif (git). Snapshot: /mnt/project-files/semver-verif/. Pipeline: pipeline/libraries/semver.
