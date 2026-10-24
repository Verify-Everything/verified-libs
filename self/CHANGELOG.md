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
