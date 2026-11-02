# Pipeline self-update log

Every change to the pipeline's own code is logged here: what changed, why, the evidence
(a note, a result, a failure), and whether the gate kept it or rolled it back.
Snapshots for rollback are in self/snapshots/.

## 2026-10-24 v0.1.0 initial build (analysis thread)
- what: vpipe CLI, toolchain setup scripts, templates, gate, fixtures, backlog.
- why: Yerin asked for a pipeline that can run on demand, update itself and implement itself.
- evidence: toolchain workarounds from general.md (crc32fast thread) and this thread's own tests.

## 2026-10-24T04:45Z Frama-C per-function summary (from a test run of `vpipe improve`)
- what: prove_framac writes prove.per_function; SUMMARY.md gets a per-function table per C library.
- why: inih test run showed 27/74 with no way to see which functions were done.
- how it got here: written by the improve agent in a scratch copy, gate passed, ported by hand.
- also: improve prompt now gets the real UTC time (the agent had made one up); __pycache__ ignored in change detection.

## 2026-10-24T04:33:24Z Lean axiom audit
- what: bin/vpipe.py `prove_lean` now runs `audit_axioms` after a passing `lake build`: a temp file (VpipeAxiomAudit.lean, deleted afterwards) imports each hand-written module and calls `Lean.collectAxioms` on every theorem in them. A theorem is `proved` only if its axioms are within propext/Classical.choice/Quot.sound; otherwise status is `nonstandard-axioms` (extras listed in `theorems[].axioms`), `sorry` (sorryAx), or `unaudited` (audit failed or theorem not found). Result gains `axiom_thms` and `unaudited`; `ok` is false if either is non-zero. SUMMARY.md gets an "Extra-axiom thms" column and a legend line. templates/prompts/lean-aeneas.md tells the agent about the audit.
- why: backlog top item and operator goal. general.md (percent-encoding) says Aeneas std models become `axiom`s in FunsExternal_Template.lean and "check `#print axioms` on each main theorem" by hand; the old code marked any theorem without a sorry warning as proved, so a theorem resting on a custom axiom would be reported proved.
- expected effect: no theorem is reported proved on a hidden axiom; each library's assumptions are visible per theorem and counted in SUMMARY.md. Caveat: the Lean snippet could not be executed in this session (no lean approval); selftest (non-full) passes, and a failing audit degrades to `unaudited` rather than a false `proved`.

- kept: selftest passed; pipeline version 0.1.1; files: ['bin/vpipe.py', 'self/BACKLOG.md', 'templates/prompts/lean-aeneas.md']
- follow-up (analysis thread, 04:50Z): ran `gate.py --full` by hand: passes. Negative test: a theorem built on `axiom cheat : False` is reported `nonstandard-axioms ['cheat']`, a `sorry` theorem as `sorry`, the real one as `proved`. Audit confirmed working.
- fix: improve now runs the full gate whenever a mathlib cache exists (it had only run the quick gate, so this Lean change went in unexercised), lets the agent run lake/lean/frama-c, and closes claude's stdin.

## 2026-10-24T05:15Z v0.1.2 lessons from the first adopted library (crc32fast)
- what: (1) Cargo.lock pinning: a reviewed proofs/<lib>/Cargo.lock (or manifest `cargo_lock`) is copied into the crate and cargo runs `--locked`. (2) install_externals keeps a `.seen` copy of each Aeneas External template; if a new run's template differs, the result lists added/removed std axioms under `extract.external_template_changes` and saves the new template as `.new`. (3) Lean agent prompt: avoid bv_decide/native_decide (they add `_native` axioms the audit rejects); act on template changes first.
- why: crc32fast thread report after adopting into the pipeline (132/132 proved): dependency drift risk, template changes only surfaced as build errors, bv_decide proofs had to be redone.
- check: full gate passes; `vpipe run crc32fast` still 132/132, 0 sorries, 0 extra-axiom theorems, no template changes.

## 2026-10-24T05:25Z v0.1.3 percent-encoding adopted natively
- what: manifest options [patches] files/dir/subtree (applied to a fresh copy before Charon), [test] commands (run on the patched tree, {src}/{tree}/{proj} expand, failure stops the run), [extract] postprocess scripts, allowed_errors, strict_externals, subdir, externals_dir, [proofs] dirs. Externals now also checked as exact rust_fun sets (from the thread's check_externals.py). Sorries inside generated code (Aeneas bodies it could not translate) are reported as generated_sorries, not against the proofs.
- why: percent-encoding thread asked for patch support, a fix-up step, -max-recdepth and a custom lakefile to run natively.
- check: `vpipe run percent-encoding` 49/49 proved, 0 sorries, 0 extra-axiom theorems, upstream tests and 2M-case differential test pass, 2.5 min; crc32fast still 132/132; full gate passes.

## 2026-10-24T05:35Z v0.1.4 Frama-C lessons from inih and Neovim
- what: default wp_args now ["-wp-rte", "-wp-literals"]; WP session cache per library (`-wp-session`, `-wp-cache update`) so re-runs only re-prove changed goals; annotated overlay files must equal upstream once ACSL is stripped (else the run fails and lists them under annotation_diffs).
- why: general.md inih section: -wp-literals is off by default and blocks strchr(";#", c); the session cache is what makes re-runs cheap; inih's strip_acsl.py diff keeps proven code byte-identical to upstream.
- check: quick gate passes; annotation check tested both ways (comment-only overlay passes, a changed `return` fails).

## 2026-10-24T06:00Z v0.1.5 every-function rule, one folder per library, portable install
- what: function inventory (scan upstream Rust/C for every function, map to Aeneas defs and theorems or WP goals, status verified/fixed/open, functions.toml overrides); SUMMARY shows Functions N/M and lists open ones; "complete" only at N/N. Layout libraries/<lib>/vpipe.toml beside the proofs (old split layout still read). One shared mathlib per key under $VPIPE_HOME/lake (symlinked). Setup: normal elan route first, `lake exe cache get` before source builds, zstd via nix/brew/apt, explicit Nix flags, VPIPE_CACHE_DIRS, retries. Subprocesses run in a local cwd (fixed a gate flake: "cannot get cwd" on the network mount).
- why: Yerin's rule (a library is finished only when every function is verified or has a verified fix); Yerin's verified-libs repo (one folder per library); toolkit thread's clean-home test (disk full, apt, nix flags, cache paths).
- check: full gate passes 3x; crc32fast 132/132 proofs but 9/43 functions; percent-encoding 49/49 but 9/26; semver 145/145 but 4/92 (model functions unmapped).

## 2026-10-24T06:10Z improve --branch
- what: in a git clone, a change the gate keeps is committed to its own branch `vpipe/improve-<UTC>` and the clone returns to its starting branch. No push; pushing and the PR stay a separate approved step (CI or a person).
- why: toolkit thread's CI (verify.yml) expects branch-per-change PRs for engine changes.
- check: tested in a scratch git repo (branch created, main untouched).

## 2026-10-24T06:55Z v0.1.6 build variants; shared mathlib after a cache download
- what: [[variant]] tables (name, cargo_args, sysroot_default, patches, aeneas_args). Each variant is its own local Lean project built from libraries/<lib>/common/ overlaid with libraries/<lib>/variants/<name>/, so module names stay the same. Extract, build and axiom audit run per variant; results under res.variants; a function counts as verified if any variant proves it (recorded per function). After `lake exe cache get` or a source build, the project's .lake/packages moves into $VPIPE_HOME/lake/<key> and is symlinked back.
- why: crc32fast's functions sit behind different cfgs (x86_64 SIMD, aarch64, portable), so no single Charon run sees them all; toolkit thread saw disk grow per project when no tarball existed.
- check: two-variant demo (host proves add_sat, riscv fails as expected for a std crate) -> function verified via host; quick gate passes; crc32fast without variants unchanged.
- incident: a test that copied the shared packages broke lake's build traces, so `lake build` called mathlib's `cache get` against the blocked server and hung for 20 min. Cleared by re-unpacking the tarball. Never copy .lake/packages; move or re-unpack it.

## 2026-10-24T07:20Z v0.2.0 admission standard (approved by Yerin 06:51) in the engine
- what: bin/standards.py (ten gates, strength labels, forbidden-construct scans, entry status, claim
  card with the verified-libs front matter) wired into every run; results gain `admission`,
  `archive_sha256`, `toolchain_digest`, `container_digest`, `clean`, `forbidden`, `crosscheck`,
  `model_crate`, per-function `label`; Lean builds are replayed with `leanchecker`. New commands:
  card, mutate (+ --suggest), check-upstream (+ --scaffold), admit, export (--dest), next, take;
  run --clean and --functions. Layout: candidates/<name>/<version>/ and libs/<name>/<version>/
  (vpipe.toml, CLAIM.md, proof/, spec/, pipeline/run.sh); libraries/<lib>/ still read. Proving is
  refused until [scope].properties is written. Zero-byte .olean check before builds.
  Frama-C: [framac] annotate script, per_function WP runs with per-function options; CBMC
  harness evidence (label capped at bounded). toolchain/soundness.toml (protected) and
  [container].digest in versions.toml. selftest checks the standards code.
- why: Yerin approved the admission standards; toolkit thread asked for leanchecker replay, archive
  SHA-256, digests, two-run reproducibility and the libs/candidates layout; Neovim thread asked for
  the annotate hook, per-function WP, CBMC evidence and a work queue; percent-encoding thread hit
  zero-byte oleans after a full disk.
- evidence: crc32fast clean run 132/132 in 2.5 min, leanchecker replay passed (14 modules, 61 s),
  CLAIM.md written, entry status candidate with 1/10 gates (correct: nothing pinned or reviewed
  yet). Planted bug `^`->`&` in fold_16 was caught. Fixture tests: annotate hook (dishonest
  annotation rejected), per-function WP 17/17, CBMC pass/fail/no-unwinding cases, take/next.

## 2026-10-24T07:25Z v0.2.1 Frama-C tool patches and complete CBMC harnesses (Neovim thread)
- what: [[framac.tool_patch]] (id, file, original, rewritten, harness, harness_files): statements
  rewritten so WP can read them. The annotation check compares against upstream with exactly these
  rewrites, and each rewrite's CBMC equivalence harness must pass with --unwinding-assertions;
  otherwise the run fails and gate 1 (real code) fails. CBMC evidence with complete = true and
  harness_files free of __CPROVER_assume keeps its declared label (e.g. full-correctness) instead of
  bounded; the reviewer checks the completeness claim.
- why: the standard forbids admit; Neovim base64 needs 4 rewrites WP's memory model can read.
- check: fixture tests (undeclared rewrite rejected, declared rewrite with passing harness accepted
  13/13, harness without unwinding assertions refused, complete vs bounded labels); quick gate passed.
- not done: Codex/Gemini agent CLIs (toolkit request). The change was blocked by this session's
  safety check; waiting for Yerin.

## 2026-10-24T07:22Z v0.2.2 Codex and Gemini as agent CLIs (Yerin approved 07:18)
- what: `--agent-cli claude|codex|gemini` on run, run-all and improve (or VPIPE_AGENT_CLI; default
  claude). codex: `codex exec -s workspace-write --skip-git-repo-check -C <cwd> --add-dir <dir>`.
  gemini: `gemini -p ... --approval-mode yolo --sandbox --include-directories <dir>`, always
  sandboxed (refuses without docker or podman). Results record agent_cli; improve's changelog line
  names the agent.
- why: toolkit thread's request; Yerin approved Codex and Gemini support with the sandboxing above.
- check: command lines built for each CLI, bad names refused; quick gate passed. codex and gemini
  are not installed in this container, so neither ran end to end here (the toolkit thread tested
  the CLIs themselves).

## 2026-10-24T07:40Z v0.2.3 function scanner fixes (crc32fast thread)
- what: the Rust scanner skips #[test], #[bench] and #[cfg(test)] functions at any level (it only
  skipped cfg(test) modules). The inventory now counts every function of the pinned upstream source
  plus every function that [patches] (or a variant's patches) add, marked added_by_patch.
- why: src/combine.rs:golden (a top-level #[test] fn) showed as an open library function; crc32fast
  patches add helpers (load128/256/512, split_quads) that must be verified too.
- check: scanner fixture (test, bench, cfg(test) fns and modules skipped; library fns kept);
  crc32fast now has 42 functions (golden gone); quick gate passed.

## 2026-10-24T07:52Z v0.2.4 listed opaque models allowed (crc32fast thread)
- what: the forbidden scan allows an `opaque` in the std/environment model files (External/ or
  *FunsExternal.lean / *TypesExternal.lean) when its name is in [trust].models, like listed axioms.
  An unlisted opaque, or an opaque anywhere else (specs, proofs), still fails gate 7.
- why: crc32fast models CPU feature flags, align_to splits and the fmt sink as opaque values and
  proves every theorem for all values; the standard allows listed models and forbids opaque in specs.
- check: fixture: listed opaque in External/ passes, unlisted one and one in a spec file are flagged;
  quick gate passed.

## 2026-10-24T07:58Z v0.2.5 pinned nixpkgs, container image name (toolkit thread)
- what: [framac].nixpkgs pins the nixpkgs revision (5adc5083, tarball URL with narHash; GitHub archive
  fallback, since github: flakes need the blocked api.github.com). setup-framac.sh builds from it with
  --out-link $VPIPE_HOME/nix/<pkg> (GC roots, so `nix store gc` keeps the tools) and records cbmc and
  nixpkgs in installed.json. [container].image added.
- why: nixpkgs floated, so native installs could differ from the container (CBMC 6.11 via nix vs
  6.4.1 via .deb).
- check: `vpipe setup framac` gives the same store paths as before (Frama-C 33.0, CBMC 6.11.0,
  Z3 5.1.0, CVC5 1.4.0, Why3 1.8.2); quick gate passed.

## 2026-10-24T08:02Z v0.2.6 first soundness-bug entry: Frama-C 33 string-literal const arrays
- what: toolchain/soundness.toml lists the Frama-C 33.0 WP bug (const char arrays initialised from a
  string literal are assumed all zeros). Bugs can now carry a `pattern` (and `unless_wp_args`):
  prove_framac scans the proved files (ACSL stripped) and fails the run on a match; such an entry is
  also marked with the bug in CLAIM.md and cannot be admitted. A declared tool patch that rewrites
  the array as a brace list removes the match.
- why: Neovim thread found the bug (verification-notes/toolchain-bugs/framac33-wp-string-init.md).
- check: fixture with `static const char alpha[] = "AB";` fails with the bug named; without it, no
  hit; quick gate passed.

## 2026-10-24T08:45Z v0.2.7 variants: functions.toml, kernel replay memory, planted bugs (crc32fast thread)
- what: (1) the function inventory reads the entry's functions.toml for [[variant]] runs too (the
  local variant build had only common/ + variants/<v>/, so declared theorems, fixes and lean= were
  ignored). (2) leanchecker replays one module per call and reports exit 137 as "killed (out of
  memory)" per module (all 23 x86_64 modules in one call ran out of memory on 15 GB). (3) `vpipe
  mutate` supports [[variant]] entries: each mutant is applied in every variant; a variant whose
  generated Lean is unchanged by the mutant is skipped ("not compiled here"); caught if any affected
  variant loses a proved theorem or fails. (4) setup installs [rust].targets (aarch64 added).
  (5) `setup lean` / `setup framac` keep the other's versions in installed.json (Frama-C versions
  were dropped, which would have hidden soundness-bug matches).
- check: crc32fast replay 14/14 modules one at a time (277 s, was 61 s in one call); trial planted
  bug in update_slow caught in all 5 variants (18.7 min for one mutant, so 10 mutants take about 3 h);
  quick gate passed.

## 2026-10-24T09:00Z v0.2.8 optional patched Charon + Aeneas (Helix "real library code" thread)
- what: versions.toml [aeneas_patched] pins the patched binaries by sha256 and lists the patch files.
  A library opts in with [extract] toolchain = "patched" (also per [[variant]]). vpipe unpacks the
  binaries only if their sha256 matches, puts them first on PATH for Charon and Aeneas, records base,
  binary hashes and every patch's sha256 in res.toolchain.aeneas_patched and extract.translator,
  folds them into the toolchain digest, and lists them in CLAIM.md under the trusted base.
  `selftest --full` runs aeneas-regress/run.sh while any library uses the patched build, with the
  shared mathlib pre-linked so run.sh does not copy .lake/packages.
- not supported: the Aeneas Lean library patch (aeneas-fdebf20-lean-lib.patch). Applying it would
  change the shared .lake/packages every library uses; it needs its own cache key first.
- check: binaries unpacked and hashes verified; aeneas-regress ALL PASS (lean: ok) with the patched
  build; quick gate passed.

## 2026-10-24T09:05Z v0.2.9 Aeneas Lean library patch in its own packages store (Helix thread)
- what: [extract] lean_lib_patch = true builds against $VPIPE_HOME/lake/<key>-leanlib-<sha12>: the
  normal packages tarball unpacked again, [aeneas_patched].lean_lib_patch applied (sha256 pinned)
  to the Aeneas checkout, and Aeneas rebuilt; mathlib is not rebuilt. A tarball of it is saved to
  pipeline/cache/ so other machines unpack it instead. The shared store is never modified. The patch
  is recorded per run and in CLAIM.md like the binary patches. No lakefile change: same Aeneas commit
  (lake prints "repository has local changes", which is expected).
- check: store built in 2.6 min (Aeneas only), tarball 572 MB; a test project sees
  Iterator.size_hint and U32.sub; the shared store shows no local changes; quick gate passed.

## 2026-10-24T09:10Z pin update: patched Aeneas build 2
- aeneas-hv-bin-x86_64.tar.gz sha256 f5bd8678… (was 85e159ef…); patch files changed too and are
  recorded per run; Charon tarball unchanged. Hashes checked on disk; aeneas-regress (7 cases): ALL PASS.

## 2026-10-24T09:12Z v0.2.10 kernel replay merged across variants (crc32fast thread)
- what: merge_variants sets prove.replay ok only when every variant's leanchecker replay ran and
  passed; failed modules are listed per variant, a missing replay as "replay not run".
- why: gate 7 read the top-level replay, which variant runs never filled ("replay not run").
- check: merge cases (all ok; one variant out of memory; one variant without replay); quick gate passed.

## 2026-10-24T09:20Z v0.2.11 peak memory per replayed module
- what: kernel_replay records each module's peak memory (os.wait4) and lists the top five as
  prove.replay.peak_gb, so the module that needs the most memory can be split.
- why: toolkit thread measured a 12.7 GB peak for crc32fast on a 16 GB CI runner, which leaves little margin.
- check: crc32fast single-target build: 14/14 pass, top module Crc32fast.Table 2.85 GB; quick gate passed.

## 2026-10-24T09:25Z pin update: patched Aeneas build 3
- aeneas-hv-bin-x86_64.tar.gz sha256 d9174f19… (enum with a reference field behind a shared borrow);
  real-code patch now 9246e123… (recorded per run). Hashes checked on disk; aeneas-regress 8 cases ALL PASS.

## 2026-10-24T09:50Z v0.2.12 patched Aeneas build 4 + Charon build 2; -filter-trait-methods
- what: pin moved to the versioned files (aeneas-hv-bin-x86_64-build4.tar.gz f41f9e7c…,
  charon-helix-bin-x86_64-build2.tar.gz 5e25172d…, patches *-build4 / *-build2), so replacing a
  plain-named file can never break the pin. Libraries on the patched toolchain get Aeneas
  -filter-trait-methods by default ([aeneas_patched].default_aeneas_args); the new-library template
  sets it too. Existing stock-toolchain libraries are unchanged (it would change their extraction).
- check: hashes checked on disk; aeneas-regress 10 cases ALL PASS; quick gate passed.

## 2026-10-24T10:02Z v0.2.13 fetch follows a changed upstream URL
- what: fetch() runs `git remote set-url origin <upstream>` on the cached clone before fetching.
- why: crc32fast moved to its published fork; the cache still fetched from the old origin ("not our ref").
- check: local two-repo test (origin moved, new commit fetched); quick gate passed.
- backlog: for fork-based entries, record the original upstream and base commit ([fork] of/base) and
  check that every function the fork changes is status = "fixed" with a proof (gate 1).

## 2026-10-24T10:15Z v0.2.14 fork check for gate 1
- what: [fork] of = <original upstream>, base = <commit>. Each run fetches the base, compares every
  function's source with the fork's, and lists changed, added and removed functions (res.fork). Gate 1
  passes only if each changed function is status = "fixed" or has functions.toml equivalence = [proved
  theorems] showing the rewrite equals the base code, and nothing was removed. CLAIM.md shows the fork,
  its base, the base archive hash and the changed functions.
- why: crc32fast now builds from Verify-Everything/crc32fast; the standard admits a fork only when its
  changes are proved fixes, and tool-readability rewrites need a proved equivalence.
- check: crc32fast fork vs upstream d2363eab: 13 changed functions (2 fixes, 11 rewrites in the
  aarch64 and pclmulqdq code), none removed; quick gate passed.

## 2026-10-24T10:25Z v0.2.15 fork rewrites accepted for gate 1
- Fork check accepts `rewrite = "<fork commit>"` in functions.toml as a third way to clear a changed
  function, next to status "fixed" and proved `equivalence`. The marker must equal the commit being
  proved, and the function must be full-correctness with every listed theorem proved. CLAIM.md lists
  these as fork rewrites that users must adopt. Basis: Yerin chose "Fork, and report overflow upstream"
  on the crc32fast decision card (09:49 UTC); the standard allows a published fork.


## 2026-10-24T10:30Z pin update: patched Aeneas build 5 + Charon build 3
- Aeneas build 5 handles for loops with early break (also fixes ropey search_by). Charon build 3
  turns edition-2018 unreachable! into a panic. sha256 values checked against the files.
- Evidence: full selftest passed, including the patched-toolchain regression suite.

## 2026-10-24T10:30Z pin update: patched Aeneas build 6 (Charon build 3 unchanged)
- Build 6 handles early returns in loops inside match arms, matches on mutably borrowed enum fields,
  and vectors of (reference, index) pairs. sha256 checked. aeneas-regress: ALL PASS (13 cases).

## 2026-10-24T10:40Z pin update: patched Aeneas build 7 (Charon build 3 unchanged)
- Loop-exit check accepts ended loans (fixes ropey merge_distribute). sha256 checked.
  aeneas-regress: ALL PASS (14 cases).

## 2026-10-24T11:00Z container digest pinned
- [container] digest set to the published toolchain image (toolkit thread, verified-libs PR #3).

## 2026-10-24T11:05Z pin update: patched Charon build 4 (with Aeneas build 7)
- Fixes erased lifetimes in associated types from trait impls (Helix ChangeIterator). sha256 checked.
- aeneas-regress: every case passes except mut_closure, which another thread added and which needs an
  Aeneas option build 7 lacks (it fails on build 7 with Charon 3 too). `selftest --full` reports
  this until the case's owner ships that build or the case moves. Not a regression from this pin.

## 2026-10-24T11:10Z v0.2.16 fork check reads functions.toml outside `run`
- fork_diff now falls back to proof_dir(lib) when the manifest has no _proof_dir, so the rewrite and
  equivalence markers are seen. Evidence: crc32fast fork diff went from 11 unfixed to 0 unfixed and
  11 rewrites (reported by the crc32fast thread).

## 2026-10-24T11:30Z v0.2.17 Aeneas build 8 + Charon build 5; Aeneas dropped-write soundness bug
- Pinned patched Aeneas build 8 and Charon build 5 (sha256 checked; aeneas-regress ALL PASS, 17 cases).
- soundness.toml: new [[bug]] for Aeneas fdebf20 (stock and patched builds 1-7): std calls through a
  shared reference to Cell/RefCell/atomics/std::sync were modelled as changing nothing. lang = "rust"
  pattern over-approximates (names Cell, RefCell, Atomic*, Mutex, RwLock, Rc, Arc...); runs on
  patched build 8 (fixed_aeneas_sha256) are exempt.
- New rust_soundness_scan: run in finish() and in `vpipe card`, comments skipped. Tested on a fake crate
  (hit found, exempt on build 8).
- Re-check of the pipeline's Lean entries: crc32fast, semver, percent-encoding have no hits in their
  proved crates (percent-encoding's only hits are in the url crate, which is not proved). No status change.

## 2026-10-24T11:55Z v0.2.18 Creusot as a second evidence type
- New [creusot] step (run_creusot): copies the entry's Creusot bundle to a local folder, runs the
  ghost-only check (annotated src minus ghost code = pinned upstream, byte for byte), the std-contract
  tests (spectest), then one `cargo creusot <entry>` per scope entry so a failure lands on exactly one
  entry. Success for an entry = exit 0, no failure mark, certificate folder present.
- functions.toml: verified_by = "creusot", creusot = [<scope entries, including helpers it relies on>].
  Verified only if the checks above pass and every listed entry proved in this run.
- Gate 7: every trusted item in the Creusot sources (#[trusted], cfg_attr(creusot, trusted), each
  extern_spec! function) must be listed in [creusot].trusted. CLAIM.md lists them.
- `vpipe setup creusot` checks `cargo creusot version` against the pin, or unpacks a pinned prebuilt
  tarball. Creusot cannot be built here (opam and gitlab.inria.fr blocked), so here those functions
  stay open with "Creusot not installed".
- percent-encoding: bundle copied to libraries/percent-encoding/creusot/, [creusot] added (19 trusted
  items, found by the scan and matching the bundle README), and PercentEncode::next, Display::fmt,
  PercentDecode::next, if_any switched to Creusot evidence (Creusot thread's request).
  decode_utf8_lossy stays open.
- Tested: trusted scan on the bundle (19 items); inventory with a simulated all-pass Creusot result
  (4 verified) and with one helper failing (the 2 decode functions go open).

## 2026-10-24T13:00Z v0.2.19 Creusot prebuilt pinned and checked in a fresh container
- [creusot].prebuilt = cache/creusot-0.14.0-linux-x86_64.tar.gz (sha256 6b5d9bef..., Creusot thread).
  setup_creusot refuses HOME other than /root (paths baked in) and installs rust nightly-2026-08-03.
- Evidence: `vpipe setup creusot` in this container (no Creusot before): installed, version matches pin.
  run_creusot on percent-encoding: ghost-only pass, spectest pass, 15/16 entries proved,
  decode_utf8_lossy fails as expected, no unlisted trusted items, 288 s. Same as the Creusot thread's run.
- run_creusot: entry folder check uses removesuffix("/*") (was rstrip of characters).

## 2026-10-24T13:10Z v0.2.20 Aeneas build 9; size_hint soundness bug under -filter-trait-methods
- Pinned patched Aeneas build 9 (sha256 checked; aeneas-regress ALL PASS, 18 cases). Charon build 5 unchanged.
- soundness.toml: new [[bug]] with requires_aeneas_args = ["-filter-trait-methods"] (patched builds
  1-8 lost size_hint overrides). Build 9 also exempt from the interior-mutability bug.
- aeneas_args() refuses -filter-trait-methods without [extract] lean_lib_patch = true. The lean-aeneas
  template now sets lean_lib_patch = true next to the flag. Extraction results record aeneas_args.
- Impact today: none. crc32fast, semver and percent-encoding never used -filter-trait-methods.

## 2026-10-24T13:35Z v0.2.21 Aeneas build 11 + Lean library patch build 10
- Pinned patched Aeneas build 11 (= build 10 + ropey descent-loop fix) and aeneas-fdebf20-lean-lib-build10.patch
  (Rust-default size_hint instead of an axiom). sha256 values checked.
- New Lean-library store built: aeneas-fdebf20-lean-4.35.0-leanlib-98b727aae0f1 (170 s), tarball in cache/.
  Removed the old local 097fb47 store (unpinned; its tarball stays in cache/ for old results).
- soundness.toml: builds 10 and 11 added to both fixed_aeneas_sha256 lists.
- aeneas-regress: ALL PASS (20 cases).

## 2026-10-24T13:40Z v0.2.22 Aeneas build 12; soundness entries matched by build number
- Pinned patched Aeneas build 12 (opaque-type region fix, not a soundness change). sha256 checked;
  aeneas-regress ALL PASS (21 cases).
- aeneas_build() reads the BUILD file in the tarball; translator_info records aeneas_build.
  soundness.toml bugs take fixed_in_build = N (sha lists kept for builds 8-11, which have no BUILD).
  Tested: build 12 exempt from both Aeneas bugs, build 7 hit by both.

## 2026-10-24T14:00Z v0.2.23 Aeneas build 13 + Charon build 6; internal errors counted
- Pinned patched Aeneas build 13 and Charon build 6 (sha256 checked; BUILD reads 13; aeneas-regress
  ALL PASS, 23 cases). Lean library patch unchanged (build 10).
- Extraction results list Aeneas "Internal error" lines as internal_errors (they can leave an axiom
  without a "Could not translate" warning; gate 7 still catches any proof that uses one).

## 2026-10-24T15:05Z v0.2.24 Lean library patch build 14; iterator size_hint soundness bug
- Pinned aeneas-fdebf20-lean-lib-build14.patch (sha256 0a300ec5...): library iterators now give std's
  size_hint instead of (0, None). New store aeneas-fdebf20-lean-4.35.0-leanlib-0a300ec58aaf built,
  tarball in cache/; old local stores removed (disk).
- soundness.toml: new [[bug]] keyed on lean_lib_patch_sha256 (the 097fb47 and 98b727 patch versions);
  soundness_hits checks the run's recorded patches. Tested: old patch hit, new patch exempt.
- aeneas-regress ALL PASS. Impact today: none (no pipeline entry sets lean_lib_patch = true).

## 2026-10-24T20:30Z v0.2.25 Lean library patch build 15; Vec::insert-at-len soundness bug (stock too)
- Pinned aeneas-fdebf20-lean-lib-build15.patch (sha256 1d9cf0a8...). New store built; old local store removed.
- soundness.toml: new [[bug]] lang = "lean", pattern Vec.insert over the generated Lean of every build
  of the library (not .lake). Exempt with lib patch build 15 (fixed_lean_lib_patch_sha256). The stock
  library is affected, so stock runs that call Vec.insert become broken.
- rust_soundness_scan also scans generated Lean for lang = "lean" bugs.
- Tested: fake extraction with Vec.insert is hit, exempt with build 15. crc32fast, semver and
  percent-encoding: 0 hits (no Vec.insert in their generated Lean). aeneas-regress ALL PASS.

## 2026-10-24T22:05Z v0.2.26 Lean library patch build 16; RawPtr.cast_scalar soundness bug (stock too)
- Pinned aeneas-fdebf20-lean-lib-build16.patch (sha256 733075b8...). New store built; old local store removed.
- soundness.toml: new lang = "lean" [[bug]] for RawPtr.cast_scalar (always fails, so proofs through it are
  vacuous), exempt with lib patch 16. Vec.insert bug also exempts lib patch 16.
- crc32fast, semver, percent-encoding: 0 hits. aeneas-regress ALL PASS.

## 2026-10-24T22:10Z v0.2.27 Lean library patch build number
- lean_lib_patch() reads a first line "# aeneas-lean-lib build N" (lib builds 17 on; 16 is the last
  without one) and translator_info records lean_lib_build. soundness.toml lib bugs take
  fixed_in_lib_build = N (Vec.insert 15, cast_scalar 16); sha lists stay for 15 and 16.
- Tested: lib build 17 exempt from both, no build and unknown sha hit by both, pinned 16 exempt.

## 2026-10-24T23:35Z pin update: patched Aeneas build 14
- A struct update of an untranslated type is now an error for that function, not a crash of the
  whole crate. Not a soundness change. sha256 checked; BUILD reads 14; aeneas-regress ALL PASS (27 cases).

## 2026-10-25T03:05Z v0.2.28 stock formatter models cap labels at no-ub
- The Aeneas Lean library's formatter models (write_str, write_fmt, debug_struct_field*_finish,
  debug_tuple_field1_finish, Debug/Display of integers and bool, ...) return Ok with the formatter
  unchanged: they ignore what is written, so output facts proved through them are vacuous.
- stock_fmt_models() finds them in the library the entry builds against (36 in fdebf20); stock_fmt_reach()
  follows the generated Lean call graph. A name the entry defines in its own externals is its own model
  and does not count. evaluate() marks each function that reaches one (not Creusot evidence), and
  function_label caps its label at no-ub. CLAIM.md says why per function. Runs in `vpipe card` too.
- Re-scored: semver 19 functions capped (Formatter Sink impl put_str/put_u64_debug, every Display and
  Debug impl on Formatter, expecting_version/comparator); generic printing over Sink is unaffected.
  percent-encoding: Display for PercentEncode::fmt reaches write_str on the Lean side (it is now Creusot
  evidence, which is exempt). crc32fast: none.

## 2026-10-26T09:40Z v0.2.29 Lean library patch build 17 (formatter output modelled); print! bug
- Pinned aeneas-fdebf20-lean-lib-build17.patch (sha256 af01d899..., header "build 17"). New store built,
  old local store removed. aeneas-regress ALL PASS (28 cases).
- stock_fmt_models: a model counts as ignoring output only if its whole body is "Ok, formatter
  unchanged" (optionally under fun ... =>), so base cases of real models no longer match.
  Stock library: 36 such models; lib build 17: 0. So entries on lib 17 are not capped.
- soundness.toml: new lang = "lean" [[bug]] for std.io.stdio._print (model returns ok, Rust panics on
  stdout failure), fixed_in_lib_build = 17.
- Re-scored: semver now defines its own write_str and DebugU64 models (its thread), so 0 capped and all
  149 proved functions are full-correctness. percent-encoding and crc32fast: no change. No _print hits.

## 2026-10-26T12:55Z v0.2.30 fork check: replaced_by for functions the fork removed
- functions.toml [[function]] id = "<upstream id>", replaced_by = "<fork id>" or [...]: a removed
  upstream function is accepted when every named replacement is verified/fixed, full-correctness, with
  all its theorems proved in this run. CLAIM.md lists "upstream function -> replacement". Unmarked or
  unproved removals still fail gate 1. (semver thread: display.rs moved into printing.rs.)
- Tested on a fake removal: proved replacement accepted, nonexistent one still fails.

## 2026-10-26T13:05Z v0.2.31 replaced_by accepts generated Lean defs (derived impls)
- A replaced_by item may be {lean = "<generated def>", theorems = [...]}: accepted only if the def is in
  the entry's generated Lean and every theorem is proved in this run. For fork code with no source id
  (#[derive] impls). CLAIM.md names the Lean def and theorems.
- Tested: real def + proved theorem accepted; missing def, or unproved theorem, still fails.
- Not done: accepting removed private helpers with no replacement. My safety check blocked it (it
  loosens gate 1); left for Yerin to decide.

## 2026-10-29T13:00Z v0.2.32 Frama-C build matrix, per-entry image, pinned WP plugins (inih)
- [framac.matrix]: one WP run per build configuration (file of preprocessor-flag lines and/or configs
  list), each with its own WP session. Rules add wp_args or set the -wp-fct list for matching lines.
  wp_timeouts retries a configuration with open goals at the next timeout. Resumable: each finished
  configuration is stored with a key over the annotated sources, flags, functions, WP args, Frama-C
  version/image, plugins and provers; a re-run reuses it while the key matches; --clean and planted-bug
  runs start fresh. smoke_tests = true adds -wp-smoke-tests; a failed smoke test keeps that function open.
- [framac] image: frama-c runs inside that docker image (work folder mounted at the same path). The
  image id and its `frama-c -version` are recorded as the run's toolchain (so soundness.toml checks the
  version that actually ran) and folded into the toolchain digest. [framac] provers overrides the pin.
- [[framac.plugin]] path + sha256: loaded with -load-module, refused on a sha mismatch, listed in
  CLAIM.md's trusted base.
- Tested on a 2-config demo with host Frama-C 33: per-config runs, rule, smoke-test failure attributed to
  the right function, resume (0 s second run). The docker path is not exercised here (image pull ran out
  of disk); command shape checked.

## 2026-10-29T13:30Z v0.2.33 Frama-C matrix fixes from the inih thread's review
- docker frama-c starts in the same folder as sh() (the annotated tree), so relative cpp args work.
- run() skips the nix Frama-C setup when [framac] image is set (no 33.0 install next to an 8.6 GB image);
  installed.json may be missing.
- All -cpp-extra-args (from cpp_args and the matrix line) are joined into one, since Frama-C keeps one.
- [[framac.plugin]] source + sha256 (pin on the source), optional build (run in the image) and output;
  the built file's sha256 is recorded, folded into the matrix key, and shown in CLAIM.md.
- Matrix rules take expect_dead = [{file, line, reason}]: a failed smoke test at exactly that place in
  a matching configuration is listed in CLAIM.md with its reason; any other dead code keeps the function open.
- Tested on the demo: relative -include works; plugin build records the output; expected dead code at
  the listed line passes only in the configuration whose rule lists it.

## 2026-10-29T13:45Z template fix
- templates/framac/manifest.toml: the expect_dead example used literal braces, which broke
  `vpipe new` (str.format). Doubled them; checked that the template formats. (inih thread)

## 2026-10-30T23:15Z v0.2.34 matrix: smoke tests only in the first pass
- A configuration retried at a longer wp_timeout no longer re-runs -wp-smoke-tests; the dead-code result
  and smoke goals come from the first pass (inih: smoke goals cost each prover's full timeout, 5+ h per
  retried config). The record notes smoke_timeout; CLAIM.md states it. Key unchanged, so finished
  configurations are reused. Trade-off: smoke tests on retried configs now use the first timeout, the
  same as on configs that pass first time.
- Tested: retried config keeps first-pass dead code; selftest passes.

## 2026-10-31T01:15Z v0.2.35 matrix rules can match one exact line
- [[framac.matrix.rule]] line = "<exact cfgs.txt line>" as an alternative to match (substring), for all
  rule fields. Needed for expect_dead: "-DINI_MAX_LINE=2" is inside "-DINI_MAX_LINE=20", and a realloc
  prefix line is inside the INI_INITIAL_ALLOC=64 lines (inih). Keys unchanged; existing match rules
  behave as before.

## 2026-11-02T00:30Z v0.2.36 planted bugs on a chosen subset of matrix configs; entry layout on every card
- mutants.toml: a mutant may name configs = ["<cfgs.txt line>", ...] (default [framac.matrix].mutant_configs).
  It is then proved only in those configurations, in its own store and sessions (tag "mutant", never
  matrix-annotated). Each named configuration must be fully proved, with no dead code, in the last real
  run (else the mutant is invalid); caught = any goal there fails or the run is not ok. A name not in the
  matrix makes the mutant invalid. Matrix keys unchanged. Without configs: the old whole-matrix behaviour.
- evaluate() (run and `vpipe card`) writes spec/README.md (if missing) and pipeline/run.sh for every entry
  under candidates/ or libs/, so hand-written entries get the verified-libs layout too (toolkit thread:
  check_structure.py). Wrote them for candidates/inih/r62-3-g2bbdec4 now.
- Tested: base 2 configs proved; mutant in one config caught (12/13) using only that config; unknown
  config rejected; separate stores and sessions.
