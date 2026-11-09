
## 2026-10-24 crc32fast: Rust → Lean toolchain setup that works in this container

Pinned stack (all must match each other):
- Aeneas release `nightly-2026.10.23-fdebf20` (Aeneas commit fdebf20d78e8007bb92fc17068f17fc2e6cfbbbf). The tarball bundles matching `charon`, `charon-driver`, `aeneas` and the Lean library sources.
- Charon 0.1.293 (inside the tarball), needs Rust `nightly-2026-09-17` with components rustc-dev, llvm-tools, rust-src, miri.
- Lean `v4.35.0`, mathlib `v4.35.0` (pulled in by the Aeneas Lean library).

What is blocked and the workaround:
- `nix build github:AeneasVerif/aeneas` fails: nix fetches github flakes through api.github.com, which this session's proxy refuses. Don't bother with nix.
- `elan toolchain install` fails: release.lean-lang.org is blocked. github.com release downloads DO work.
- So: download everything from github.com/…/releases/download.

Steps (about 5 minutes, plus mathlib fetch):
```sh
# Aeneas + Charon binaries
mkdir -p ~/tools/aeneas && cd ~/tools/aeneas
curl -sSL https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.10.23-fdebf20/aeneas-linux-x86_64.tar.gz | tar xz
# Rust nightly for Charon
rustup toolchain install nightly-2026-09-17 --profile minimal -c rustc-dev,llvm-tools,rust-src,miri
# Lean via elan, toolchain fetched manually
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
apt-get install -y zstd
cd ~/tools && curl -sSL https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst | tar --zstd -x
~/.elan/bin/elan toolchain link leanprover--lean4---v4.35.0 ~/tools/lean-4.35.0-linux   # shows up as leanprover/lean4:v4.35.0
```
Lean project: `require aeneas from git "https://github.com/AeneasVerif/aeneas.git" @ "<aeneas commit>" / "backends/lean"`, `lean-toolchain` = `leanprover/lean4:v4.35.0`.

Charon tips:
- Use `charon cargo --preset=aeneas --dest-file X.llbc -- <cargo build args>`.
- To avoid SIMD/arch-specific code without editing the source, build for a target where the `cfg` picks the portable path: `-- --no-default-features --target riscv64gc-unknown-none-elf` (add with `rustup target add --toolchain nightly-2026-09-17 riscv64gc-unknown-none-elf`). This only works if the crate is no_std-capable.
- For a cross target, add `--sysroot default`. Without it Charon tries a miri full-MIR sysroot and the build lost its dependency (`can't find crate for cfg_if`).
- Aeneas: `aeneas -backend lean -dest out X.llbc` (single file). It warns about missing models (e.g. `Step::forward_overflowing`), which is harmless if unused.

## 2026-10-24 crc32fast: mathlib cache is blocked, so mathlib builds from source

- `lake update` / `lake exe cache get` cannot download mathlib's prebuilt files: cache.mathlib.org (and the old Azure mirror) are refused by this session's network policy. Lake falls back to compiling mathlib, which takes a long time (measuring now; see crc32fast.md).
- Aeneas's Lean library imports mathlib, so every Rust→Lean thread hits this.
- Fix for future sessions: allow `cache.mathlib.org`, `release.lean-lang.org` and `api.github.com` in the cloud environment's network settings (asked Yerin).
- Until then: once crc32fast's build finishes I will tar the built `.lake/packages` (Aeneas fdebf20 + mathlib v4.35.0) to `/mnt/project-files/verification-notes/cache/` so other threads can unpack it instead of rebuilding. Check that folder before starting your own mathlib build.

## 2026-10-24 semver: more blocked hosts, and a fallback if no Aeneas release tarball fits

- opam is unusable here: opam.ocaml.org is refused, and most OCaml package sources live on refused hosts (erratique.ch, gitlab.inria.fr, download.camlcity.org, ocaml.janestreet.com) or are github `/archive/` tarballs, which also get 403. Plain `git clone` from github.com works.
- Prefer the Aeneas release tarball described above. semver also uses `nightly-2026.10.23-fdebf20` so all Rust threads share one pinned stack.
- Fallback that works if you need to build Aeneas from source: Nix with the binary cache. cache.nixos.org and releases.nixos.org are reachable. Install nix from `https://releases.nixos.org/nix/nix-2.31.2/nix-2.31.2-x86_64-linux.tar.xz` (`./install --no-daemon`, with `/etc/nix/nix.conf` holding `build-users-group =`, `sandbox = true`, `ssl-cert-file = /root/.ccr/ca-bundle.crt`). Get nixpkgs by `git fetch --depth 1` of the commit pinned in Aeneas's flake.lock (not the github tarball), set `NIX_PATH=nixpkgs=<that clone>`, and `nix-shell` a list of `ocaml-ng.ocamlPackages_5_2` deps. easy_logging isn't in nixpkgs: git clone it, copy `easy_logging/`, `dune-project` and the opam file into `aeneas/src/vendor/el/`, and delete its examples dir and the examples rule in its dune file. Charon from source needs `git submodule update --init` (minirust) and skip charon's `make format` step.
- Keep `sandbox = true` in nix.conf. With it off, a build leaves `/homeless-shelter` behind and every later build refuses to run.
- Don't `pkill -f "cache get"`: it matches and kills your own shell too.

## 2026-10-24 percent-encoding: more setup findings (Aeneas/Lean)

- **Mathlib cache is blocked**: `lake exe cache get` fails because `cache.mathlib.org` (and the older `lakecache.blob.core.windows.net`, `mathlib4.lean-cache.cloud`) are refused by the proxy. Mathlib gets built from source by `lake build` (Aeneas only needs a slice of it, but expect a long first build). Yerin can fix this for future sessions by allowing `cache.mathlib.org` in the cloud environment's network settings.
- `zstd` is not installed and apt may not be needed: `nix shell nixpkgs#zstd` pulls it from cache.nixos.org, which IS reachable.
- Nix route for building Aeneas from source does work if you replace every `github:` flake input with `git+https://github.com/...?rev=...&shallow=1` (git clones are allowed, GitHub archive tarballs and api.github.com are not). Script: generates `--override-input` flags from flake.lock. The release tarball (see crc32fast section) is much faster, so prefer it.
- Charon on a crate with `alloc`/`std` features: `-- --no-default-features` keeps you to the no_std core and avoids Cow/String/Vec models.
- **Aeneas unsupported patterns seen (and the source rewrite that fixed each)**:
  - "Early returns inside of loops are not supported yet": rewrite `for (i, x) in it.enumerate() { if p(x) { ...; return ... } }` into a `while i < len && !p(s[i]) { i += 1 }` index search followed by the shared tail.
  - Closures (`opt.map(|x| ...)`): rewrite to `match`.
  - `impl Display` that loops over a cloned iterator, and derived `Debug` on a struct holding `slice::Iter`: fail ("Joining region abstractions..."/"Unimplemented"). They come out as `sorry`; leave them out of scope.
  - Keep rewrites in a patch file, run the upstream test suite on the patched crate, and state the rewrite in the report.
- Missing std models come out as `axiom`s in `FunsExternal_Template.lean` when you pass `-split-files`. Copy it to `FunsExternal.lean` and replace the ones your proofs touch with `def`s (e.g. `from_utf8_unchecked := ok` since `Str := Slice U8`; `char::to_digit`; `u8::is_ascii`; `Option` `?` branch). These defs are trusted assumptions: list them in the report and check `#print axioms` on each main theorem.

## 2026-10-24 Neovim: C toolchain (CBMC + Frama-C WP) that works in this container

Install (about 2 minutes total):
- CBMC: not in Ubuntu apt. The github release .deb downloads fine with plain curl (`gh api` is refused, the direct URL works):
  `curl -sSLO https://github.com/diffblue/cbmc/releases/download/cbmc-6.4.1/ubuntu-24.04-cbmc-6.4.1-Linux.deb && dpkg -i *.deb; apt-get -f install -y`
- Frama-C: apt's `frama-c-base` (v25) has **no WP plugin**, so it can't prove contracts. opam is blocked. What works: Nix binary cache, which gives Frama-C 33 with WP in ~30s:
  `nix --extra-experimental-features 'nix-command flakes' profile install nixpkgs#framac nixpkgs#z3 nixpkgs#cvc5 nixpkgs#why3` then `export PATH=/root/.nix-profile/bin:$PATH; why3 config detect`. (nix was already at /nix/var/nix/profiles/default/bin in my container.)
- Skip Alt-Ergo: nixpkgs marks it unfree. Z3 + CVC5 were enough.
- `/mnt/project-files` is mounted noexec: run scripts there with `bash script.sh`, not `./script.sh`.

CBMC lessons (bounded model checking of C):
- Use one exact input length per run (`__CPROVER_assume(n == LEN)`), not `n <= MAX`. A symbolic length up to 5 ran out of 15 GB RAM; exact lengths 0..32 all finish in seconds, and run 4 at a time.
- Compile the upstream .c file unmodified. Put stub headers in a `-I stubs` dir for the project's internal headers (config, memory allocator, generated headers). Model "malloc that never fails" with `__CPROVER_assume(p != NULL)`.
- Free everything in the harness, or `--memory-leak-check` fails on the harness itself.
- `--conversion-check` flags `(char)int_in_128..255`, which is implementation-defined, not UB. Leave it off or expect noise.
- Always run a mutation check: plant a handful of known bugs with sed and confirm a harness fails for each. Fast proofs can be vacuous; this is the cheap way to know they aren't. Template: `/mnt/project-files/neovim-verify/mutants.sh`.
- A reference model written byte by byte (no tricks) is a good spec for optimized code (e.g. a 64-bit-at-a-time fast path).

Frama-C WP lessons (unbounded proofs of C):
- Keep ACSL annotations in a patch against a copy of the pinned upstream file. Re-running on a new release = apply patch, re-prove. Template: `/mnt/project-files/neovim-verify/framac/run_wp.sh`.
- `-wp-model Typed+Cast` when code casts `char*` to `uint8_t*`. The typed model then treats the two views as separate memory; state the link you need as an explicit precondition and list it as an assumption. `-wp-model Bytes` handles casts but was slower and proved less.
- SMT solvers can't reason about `&`, `<<`, `>>` on unbounded integers. Turn them into arithmetic with small ACSL lemmas (`(x & 4095) == x % 4096`, `(x << 6) == x * 64` for bounded x), use them via `assert`, and check the lemmas separately with Z3 bit-vectors (Python `z3-solver` from pypi works; see `framac/check_lemmas.py`). WP's own lemma proofs time out.
- WP does not model fresh allocation (`\fresh`, `allocates`, `\freeable` are ignored), so an `assigns` clause on a function that writes into a buffer it just malloc'd can't be proved. Drop the assigns clause and say so.
- Add `-DNDEBUG` so `assert()` calls don't become extra goals.
- Debug a stuck goal with `-wp-prover none -wp-print > goals.txt`: Qed sometimes simplifies a hypothesis away (it turned `land(4095,x) <= 4095` into nothing), and you only see that in the printed goal.
- Write invariants for exact counters (`out_i * 8 + acc_len == 6 * src_i`), then prove buffer bounds with a few case-split asserts. This closed every bounds goal in the Base64 decoder.

Pipeline idea from this run: CBMC (bounded, quick, finds bugs, no annotations) as the first pass on every target, then Frama-C WP for the functions worth an unbounded proof. Run the mutation check on every pipeline run, since it also detects when upstream changed enough for the harness to go stale.

## 2026-10-24 crc32fast: Lean proof patterns for Aeneas output (all proved, standard axioms only)
- **Avoid `bv_decide` if you want a clean audit.** It adds `_native.bv_decide` axioms (trusts the
  compiled checker), and the pipeline's axiom audit then reports the theorem as not proved.
  Kernel-checked replacements that worked: (1) prove linearity once (`bitStep (x ^^^ y) = ...`)
  by `cases` on the low bits, then derive the rest by rewriting; (2) bit-by-bit identities with
  `apply BitVec.eq_of_getLsbD_eq; intro i hi; iterate 32 (rcases i with _ | i; · simp ...); omega`
  (macro `bv_bits` in `pipeline/proofs/crc32fast/Crc32fast/Bits.lean`); (3) `bv_omega` for
  bounds like `v >>> 24 < 256`. Use `getLsbD`, not `ext`/`x[i]`: simp cannot rewrite `(a ++ b)[i]`
  once the width is normalised to 32. A `getLsbD_le32`-style lemma for concatenations fixes it.
- **Spec state equality via a basis.** For GF(2)-linear maps on BitVec 32, prove linearity, then
  compare on the 32 basis vectors with `decide +kernel`. Keeps every `decide` small.
- **`decide +kernel` handles big tables.** 4,096 table entries vs the spec in ~6 s.
- **Binds.** Aeneas output uses both `Std.bind` and `Bind.bind`; a macro
  `first | rw [bind_ok] | rw [bind_tc_ok]` steps one bind. `rfl` does not reduce binds.
- **Literals like `16#usize`** carry proofs that break `simp`/`dsimp` ("motive is not type
  correct"); state helper lemmas over `Usize.ofNat n hn` and use `rw` or `show`.
- **Loops.** Write an unfold lemma for the generated `_loop` def, then prove the loop by
  induction on a measure with separate lemmas for the `some` (body) and `none` (exit) steps.
- **External models.** Replace the template's axioms (wrapping_neg, unwrap_or_else,
  Option::clone, `?` branch/from_residual) with definitions; then they are not assumptions.

## 2026-10-24 inih: Frama-C WP pitfalls (C threads read this)

- **Run the container as root on a mounted dir** (`docker run -u root -e HOME=/home/opam ...`). The image's default user can't write to a root-owned mount, every prover call fails with `Sys_error("Permission denied")`, and with `-wp-cache update` those failures get cached. `frama-c/fc.sh` now does this.
- **`-wp-no-pruning` can be a 15x speed-up.** On inih's main loop (one big function, many branches) Qed spent 40-50 s per goal in its "prune trivial branches" pass. `-wp-no-pruning` brings that to about 3 s and keeps Qed's other simplifications. (`-wp-no-let` is even faster to generate but leaves huge unfiltered goals that the provers then time out on.)
- **`-wp-literals` is off by default.** Without it WP doesn't know the contents of string literals, so `strchr(";#", c)` can't even prove its `valid_read_string` precondition.
- **Pointer comparisons don't imply the same block.** `p <= q` in WP compares offsets only. Add `\base_addr(p) == \base_addr(\at(p, Pre))` to loop invariants that walk pointers.
- **Logic functions like `strlen` aren't framed after writes.** After any write, WP no longer knows `strlen(s)` even if the write is elsewhere. State facts at `Pre` (`\at(strlen(src), Pre)`) or as per-cell facts (`s[k] == '\0'`, `\forall j < k, s[j] != '\0'`), which WP does carry across unrelated writes.
- **Local array initializers are only partly modelled.** `char section[50] = "";` gives WP only `section[0] == 0`, not the zero-fill of the rest. Don't write invariants that rely on the zero-filled tail.
- **Function pointers:** WP needs a known callee. Redirect the calls with function-like macros in a prelude passed via `-include` (`#define reader(...) proof_reader(__VA_ARGS__)`) and give the abstract function a contract describing every allowed implementation. Non-call uses of the name (parameter declarations, `assert(reader != NULL)`) are untouched.
- Keep annotated proof copies honest: strip `/*@ */` and `//@` and diff against upstream (inih's `strip_acsl.py`).
- `-wp-session <dir> -wp-cache update` stores prover results under `<dir>/cache`, so re-runs only re-prove changed goals.

## 2026-10-24 percent-encoding: finished; Aeneas proof patterns and library gaps

Result: full functional correctness of encoder + decoder + round trip, standard axioms only. Bundle and re-runnable script: `verification-notes/percent-encoding/` (`bash pipeline/run.sh`, 1.5 min fresh with the shared cache). Things worth reusing:

- **Gaps in the Aeneas Lean library (release fdebf20)**, fixed by `percent-encoding/pipeline/postprocess.py` after each extraction:
  - Generated code calls `U32.rem` (from a const `<<` in Rust), which does not exist. Replace with `a % b`.
  - Generated `Iterator` trait instances set `size_hint := ...`, but the library's `Iterator` structure has no such field. Delete the field.
  - A 768-element array literal hits `maxRecDepth`: pass `-max-recdepth 16384` to aeneas.
  - `UScalar.wrapping_shl` is not `@[expose]`, so from a `module` file you cannot evaluate it (decide gets stuck, no lemmas exist). Put such proofs in a plain non-`module` file (`import ...`), where the body is visible.
- **Spec style that worked**: a pure reference spec on `List Nat` (encode/decode as ordinary recursive functions), lemmas on the spec alone (round trip etc.), then one `⦃ ⦄` step theorem per Rust function relating it to the spec. For iterators: prove a spec for one `next` call ("chunk ++ spec(rest) = spec(input)", length decreases), then define a fuel-bounded `collect` in Lean and prove it equals the spec by induction on fuel.
- `step*` does most of the work. Typical finishing kit: `subst_vars`, `simp_all`, `scalar_tac`, `split at h` on `match` postconditions, `getElem!_pos l i h` to turn `l[i]!` into `l[i]`.
- **Orientation matters for simp_all**: write postconditions as `hexVal c = r.map (·.val)` (spec on the left), not `r.map ... = hexVal c`, otherwise simp_all rewrites `none` into `hexVal c` and gets stuck.
- Lookup tables and finite facts: `decide +kernel` over `∀ n < 256, ...` works (768-byte table in ~10 s) and stays kernel-checked (no `native_decide`).
- Writing models in FunsExternal.lean: keep the generic signature but make proofs easy, e.g. `size_of (T : Type) := if T = U32 then ok 4 else fail .panic` (check the used type first so you never need `U32 ≠ U8`). `Str` is `Slice U8`, so state specs with a helper `strBytes (s : Str) := bytes s` to avoid Str/Slice type-mismatch errors in simp.
- `pkill -f <pattern>` inside the Bash tool kills the tool's own shell when the pattern appears in the command line. Use `ps` + `kill <pid>`.
- `/mnt/project-files` is noexec: run scripts there with `bash script.sh`.

## 2026-10-24 semver: proof patterns for parsers (Aeneas + Lean)

- **Strengthen callee specs with bounds** in the postcondition (`numM .. = resMap .. r ∧ ∀ p, r = .Ok p → p.2 ≤ len`). Then `step*` on a big caller discharges the index/bound side goals by itself.
- **`?` operator**: the library's `branch.step_spec` gives a `match r with ...` post that `simp_all` can't use. A local `@[step]` spec with post `(∀ v, cf = .Continue v → r = .Ok v) ∧ (∀ res, cf = .Break res → ∃ e, r = .Err e ∧ res = .Err e)` is picked over the library one and lets one `simp_all` close every leaf. 200-line nested parser went from stuck to proved this way.
- `step*` stops at `let (a, b) := val`; `obtain ⟨a, b⟩ := val; step*` continues.
- **simp loops to avoid**: a lemma `l[i] = l[i]!` in a `simp_all` set loops (simp normalizes back); apply it with `simp only [..] at *` first. `(a = b) ↔ a.val = b.val` for Usize also looped in simp_all. "maximum recursion depth" escapes `first | ...`, so bisect the simp set.
- `rw` cannot rewrite an `if` condition (Decidable instance in the motive); `simp only [h_iff]` can.
- `rcases r with a | e` on `core.result.Result`: Ok comes first.
- For list-index proofs, state positional lemmas against `s = A ++ x :: C` with `k = A.length` (not raw arithmetic), and keep any digit byte opaque (`obtain ⟨d, hd, _⟩`) so `simp` never sees `UScalar.ofNat` proof terms (they caused recursion-depth blowups).
- Register libraries whose upstream needs a safe model with vpipe by shipping the model as a patch that *adds* a crate folder, `crate_dir = "model"`, and the differential test as `[test]`.

## 2026-10-24 inih: more WP lessons for big C functions

- **Avoid pointer subtraction (`p - q`) in contracts when one side is a local array.** WP's default model can't subtract a pointer into a local array (`line + offset`) from a pointer returned by a call; it prints `Uncomparable locations ... Hide sub-term definition` and silently drops the fact, so many unrelated goals time out ("Stronger" in the status). Write ranges without subtraction instead: `\exists integer n; end == s + n && \valid(s + (0..n))`, `s + strlen(s) <= end`, and assigns as a set: `assigns { *p | char* p; \base_addr(p) == \base_addr(s) && s <= p < end };`. Don't use `\offset()` as a workaround: WP can't relate it back to pointer arithmetic.
- **Pointer `<`/`<=` only compares offsets.** In `\forall char* p; s <= p < e ==> ...` always add `\base_addr(p) == \base_addr(s)`, or even trivially-true invariants become unprovable.
- **Breadcrumb asserts beat long timeouts.** A loop invariant about one buffer timed out at 150 s because provers had to chain about 15 memory states through calls. Restating it as `//@ assert` right after each call that writes memory brought every goal under 30 s.
- **Ghost index instead of an existential.** For "this buffer holds a NUL somewhere" use `//@ ghost int k;` plus the invariant `buf[k] == '\0'`, and after a write recompute `k` with a small ghost loop. An `\exists` invariant was unprovable.
- **Statement contracts don't cut the VC.** WP still inlines the block body into the goals, so they don't help with size.

## 2026-10-24 semver: more Aeneas + Lean lessons

- `bv_decide` proves goals through a native-code axiom (`Lean.ofReduceBool`), which the pipeline's axiom audit rejects. Use `bv_omega` for add/sub goals, and `ext i hi` with the `BitVec.getElem_*` lemmas for rotations and shifts. Both are kernel-checked.
- Aeneas rejects byte-string literals (`b"..."`: "There should be no bottoms in the value"). Array literals work (`push_all(out, &[109, 97, 106])`). Generate them from a script if there are many messages (semver: model/gen/printing.py).
- Derived `Clone`/`PartialEq` on a struct with an `Option` field pull in std's Option impls as Lean axioms. If only tests need them, gate them: `#[cfg_attr(feature = "debug", derive(Clone, PartialEq))]`.
- For a std function you must trust (semver: `Debug for char` on non-ASCII, which needs Unicode tables), keep it in its own small function and pass `charon --opaque crate::path::fn`. It becomes one named axiom in FunsExternal.lean, which is easy to audit.
- Aeneas copies the code after an `if` into both branches. A long function with several `if`s grows into a large tree that slows proofs. Split it into small functions with tuple results; each gets its own spec.
- An inline `a < len && s[a] == b` becomes a bind inside an `if`, which `step*` cannot get past. Put it in a helper (`byte_at_is`) with a one-line spec.
- In `loop.spec_decr_nat`, annotate the lambda binder types (`fun (x : Usize) => ...`). Without them elaboration can time out.
- Error kinds that carry a `char` can be modelled exactly by storing the byte offset of the char in the input. Then the differential test can compare full error messages, not just kinds. This caught a wrong kind in semver's model (`Prerelease::new` returns IllegalCharacter, not UnexpectedCharAfter).

## Helix, 2026-10-24 (update_positions)
- Upstream code that claims to "handle unsorted input" is a good place to look for bugs: the sorted fast path gets the tests, the unsorted fallback rarely does. A differential test that shuffles inputs found it in seconds.
- For a loop with a "rewind" path, prove the sorted case and the fixed version with one invariant parameterised by a `fixed : Bool` flag. One proof covers both, and the measure gets an extra term only when a rewind is pending.
- Aeneas/Lean: `let (a, b) := (r, ...)` tuple lets in goals block `simp only [h]` on the inner `if`; run `simp only [step_simps]` first. Facts like `¬ (1#u8 = 0#u8)` need `congrArg UScalar.val`, not `decide`.

## Helix selections, 2026-10-24 (Aeneas/Lean)
- Aeneas's `Vec.insert` model requires i < len, but Rust allows i == len (append). Model code that may insert at the end should push in that case.
- Charon runs on a real multi-crate workspace (helix-core): move the workspace `rust-toolchain.toml` aside first (Charon needs its own nightly), then `charon cargo --preset=aeneas --start-from 'crate::module'`. Other crates come out opaque. Aeneas crashes on fn items used as closures (`sort_unstable_by_key(Range::from)`); mark those impls opaque.
- Lean packages: symlink a new project's `.lake/packages` to `~/lakepkgs/.lake/packages` instead of re-downloading. zstd is at `~/.vpipe/bin/zstd` after bootstrap.
- To check name clashes between proof files written by parallel workers, write one file that imports every module and `#print axioms` each theorem; it also gives the axiom audit in one run.
- `let*` on a pair result destructures it: `let* ⟨ a, b, post ⟩ ← f_spec`. For flattened loop invariants use `refine ⟨by scalar_tac, ?_, by scalar_tac⟩`. Postconditions Aeneas simplifies to `True` need `trivial`, not `rfl`.

## 2026-10-24 semver: running Aeneas on real upstream code
- `charon --preset=aeneas` on a crate using `str` patterns crashes Aeneas ("Unimplemented ... str/pattern.rs").
  `--exclude 'core::str::pattern'` gets past it; the str methods then land as axioms in FunsExternal.
- Unsafe raw-pointer code (ptr::read/write, alloc, NonNull) also lands as axioms. Those axioms have no
  meaning in Aeneas's pure model, so unsafe parts need a second tool and a linked spec.
- "Returns inside of nested loops are not supported yet" drops the whole function body (semver display::pad).
- Under the admission standards, a model crate is only a candidate. Run this upstream test FIRST on a new
  library, before writing a model, to see how much of the real code Aeneas can read.

## 2026-10-24 Helix parsers: real-code extraction with no axioms left (worked end to end)
- Do NOT mark core/alloc/std `--opaque`: Aeneas then crashes on its own builtin types (RangeFrom etc.).
- After `--exclude 'core::str::pattern'`, the Lean has `«sorry /- Could not find: trait_decl_id -/»` holes
  where the Pattern trait was. A sed swap to a hand-written `core.str.pattern.Pattern` structure (char
  instance = the char's UTF-8 bytes) closes them. Script: helix-verify/utils-real/extract.sh.
- Replace FunsExternal axioms by `def`s (helix-verify/utils-real/lean/HelixReal/StdModels.lean: str len/find/
  contains/index by a.., ..e, a..e, Option::map_or). Std methods nothing calls can be `fail .panic`: that only
  makes proofs fail, never pass wrongly.
- In this Aeneas, `Result` is a coinductive tree, not an inductive: you cannot `match r with | ok x`. Use
  `Option.ofResult r` (or `r.match`). This is also how to run Lean std models in `#eval`.
- Difftest of std models against real std without compiling a Lean exe: a Rust program writes inputs plus std
  results to a file; a Lean file `#eval`s the models on each line (100k cases in ~17 s). See utils-real/stdtest.
- `omega` can fail with "Application type mismatch ... Coeffs" when the context has `⋯.choose` atoms;
  prove the arithmetic fact earlier (before those hypotheses) and reuse it.
- Concrete evaluation of extracted functions via `simp` is painful (loop is partial_fixpoint, Str vs Slice U8
  types block bind_ok). Keep bug witnesses as runs of the real Rust code instead.

## Helix parsers (sniprender)
- Aeneas on real helix-core: Charon works, but Aeneas hits internal errors on core `Iterator`, slice iterators and `map`/`flat_map` closures. It also rejects `dyn` trait types ("not supported yet") and `str::strip_suffix` ("Unimplemented"). To get a buildable partial extraction, `--exclude helix_core::path::_::fn_name` the offending functions (an impl in the middle of a path is written `_`). Callers of excluded functions become axioms. `--start-from` does not accept `_` impl patterns.
- Use `abbrev`, not `def`, for stand-in external types (e.g. `HashSet T := List T`) so that simp can see through them. Define the hash/default instance stubs too, or they show up in `#print axioms`.
- To prove a hang (divergence) on extracted code, use `dspec (f x) (fun _ => False)` via `loop.fixpoint_induct body P` with `Lean.Order.admissible_pi` + `dspec_func_admissible`. Give explicit type annotations on the admissibility lambda.
- Simp tips for Aeneas output: `Std.bind_ok` (plain `bind_ok` is ambiguous), `_root_.dite_true`, and `simp only [uncurry]` for `let (a, b) ← …`. For Usize subtraction, unfold `UScalar.sub` (it is `if x < y then fail else ok`).
- `update_positions` on an unsorted position list is not equal to per-position `map_pos`. Only compare them on sorted input.
- Charon `--include 'crate::path::Type'` inside an `--opaque` crate makes just that struct transparent. For helix, `--include helix_stdx::range::Range` turned 8 "Internal error"/"Ignoring the body" functions (closures reading `range.start`) into clean extractions; `--include helix_core::snippets::elaborate::Tabstop` did the same for `prepare_render` ("Unexpected error" on a field read). Try this before any flag sweep: `--hide-marker-traits`, `--monomorphize(-mut)`, `--lift-associated-types '*'` (there is no `--remove-associated-types`) fixed nothing here. Run it under `set -f` so `*` is not globbed.
- Aeneas emits `map`/`collect`/`position` fields in `Iterator` impls that the Aeneas Lean `Iterator` structure lacks: delete them from the generated `Funs.lean` (mark the edit).
- Loops in proofs: prove one generic loop lemma (body `B` as a parameter, with `hend`/`hstep` hypotheses) and instantiate it with `refine Exists.imp (fun .. => ..) (lemma .. ?hend ?hstep ..)`, so `B` unifies with the extracted lambda. Restating the lambda by hand fails because the matchers differ. Aeneas's `Vec::from_iter` (`FromIteratorVec.iterToList`, a partial_fixpoint) unfolds with `rw [alloc.vec.FromIteratorVec.iterToList]`.
- For `Vec` values, use `alloc.vec.Vec.from_val` (`(Vec.from l h).val = l`); `rfl` does not close it.
- Charon on a big workspace fills the disk via incremental build dirs: set `CARGO_INCREMENTAL=0` and delete `target/` after each extraction.
- Aeneas `-filter-trait-methods` removes the trait-impl methods (e.g. `map`/`collect`/`position` in an `Iterator` impl) that the Lean library's trait structure lacks, so no hand edit of `Funs.lean` is needed. `-all-computable` makes the output `#eval`-able for gate 8. Stand-in axioms that the code still references (derive Debug/PartialEq helpers) then block compilation: `@[implemented_by f] axiom ...` gives them runtime code and keeps them axioms for `#print axioms` (script: helix-verify/snippets_render/tools/g8ext.py; merge it into the existing `@[rust_fun ...]` block, since two attribute blocks do not parse).
- Gate 8 for code taking structs with private fields: append the generator as a `#[cfg(test)] #[path] mod` to the module that defines them, so it can build states directly and call private fns. Flag every line that falls outside a stand-in's scope (e.g. `Selection::new` vs normalize) and report those lines separately rather than dropping them. A planted-bug patch applied to the Rust tree, with the Lean side unchanged, shows the checker can fail.
- In Lean `do` blocks inside `#eval` files, `name` cannot be used as a variable ("ill-formed syntax"), and `for (a, b) in` failed here too: bind the pair and project it.
- Non-vacuity witnesses for Aeneas specs: a WP conclusion `f x ⦃ r => P r ⦄` becomes a concrete fact via `spec_mono h (fun r hr => …)`. A `dspec … (fun _ => False)` conclusion gives `f x ≠ ok v` via `rw [e, dspec_ok] at h`. Discharge a precondition like `primary_idx s sel = ok p0` with its own spec applied to the concrete data. Mathlib `interval_cases` may not be imported; `rcases i with _ | _ | _ | i` + `omega` works. (sniprender, 2026-10-26)
- Contrary to the line-512 caution, Lake 4.35 here DID rebuild importers after a body-only edit of `Real/X/Funs.lean` (the proof then failed as expected). Still check the importer olean mtimes after each mutant. (sniprender, 2026-10-26)

## 2026-10-24 Helix text helpers: Aeneas and char literals (real code)
- Aeneas rejects `match` on char literals ("Unsupported switch scrutinee", whole body becomes sorry) and cannot print
  non-ASCII char literals (emits `sorry`). Two LLBC passes fix both without touching upstream source:
  helix-verify/real-common/tools/lower_char_switch.py (char switch -> chain of `s == lit` bool switches, each branch
  kept once) and nonascii_chars.py (non-ASCII literal -> control-char placeholder, then `Char.ofNat 0x..` in the Lean).
  They need `charon ... --no-dedup-serialized-ast`. Example pipeline: helix-verify/text/real/EXTRACT.md.
- Char externals: Aeneas `Char` is Lean's Char. Rust char order = `compare a.toNat b.toNat`; `RangeInclusive::contains`
  must be modelled as std does it (start <= x, and x <= end, x < end once exhausted). Proof tip: `Char.toNat_inj`,
  and `show (Char.ofNat 0xA0).toNat = 0xA0 from rfl` for literals.
- Aeneas's `core.fmt.Formatter.write_str` is a no-op on an opaque Formatter: Display/Debug output cannot be proved with
  the stock Aeneas library. It needs a Formatter that records the written bytes (vendored Aeneas change).
- Tables for char -> X functions (std is_alphanumeric/is_whitespace, unicode-general-category, unicode-width) can be
  generated by running the real function on every char (1.1M values): the Lean table then equals the function on all
  inputs. Generator: helix-verify/text/gen.
- Kani with symbolic sizes but no loops (calloc/memcpy models, `--default-unwind 2` + unwinding assertions on) gives
  unbounded results for unsafe pointer code: see helix-verify/text/kani (GraphemeStr).

## 2026-10-24 percent-encoding: meeting the admission standards with Aeneas (lessons)
- Run Aeneas on the UNPATCHED crate first and keep the error list: it is exactly the set of functions that need a second tool for gate 1. Charon `--monomorphize`/`--monomorphize-mut` and Aeneas `-loops-to-rec` did not remove nested-borrow, closure or early-return-in-loop errors.
- Extracted Aeneas code CAN be evaluated in Lean (`lake env lean --run file.lean`): observe a `Result` with `r.match` (`.ok a | .vis _ _ | .div`), not by pattern matching on `ok`. One `noncomputable` model poisons everything that uses it (here a Classical `if T = U32` in `size_of`); make models computable and guard any narrowing with a postprocess check.
- That gives two cheap differential harnesses: std models vs real std (gate 7 "each model tested"), and extracted crate vs compiled upstream (gate 8). Build `Slice` with `Slice.from l h`; `Slice.mk` takes 3 fields now.
- Make unsafe-precondition models fail (`if Utf8Valid s.val then ok s else fail .undef`): the proofs then show no UB instead of a side argument. `step*` leaves the precondition as an extra goal before the main one.
- A replacement for an `opaque` model: Rust's from_utf8_lossy = "substitution of maximal subparts" (Unicode Table 3-7 lead-byte ranges); a 40-line Lean def matched std on 672k inputs.
- Disk: a disk-full during `lake build` leaves zero-byte .olean files that later fail with "invalid header"; delete them (vpipe 0.2.0 now checks).

## Helix parsers (cmdline)
- Charon `--start-from` patterns: an inherent method is `crate::mod::Type::method`, without generics or lifetimes (`Type<'_>`, `Type<'a>` and `Type<_>` all fail). A trait impl is `{impl core::default::Default for crate::mod::Type}`. Impls of generic traits (`Index<usize>`) and impls on `&Type` are rejected. A wrapper fn in a scratch copy is the workaround.
- Anything that reaches `core::str::pattern::Pattern` (`find`, `split_once`, `ends_with`, `trim_*` with a pattern) crashes Aeneas fdebf20 with `CFailure`, also with `--opaque core::str`. `Iterator::find` on slices fails with "lifetime constraint relating". `Box<dyn Error>` fails with "Dynamic trait types". `Option::map(AsRef::as_ref)` gives "Internal error", and the output has `sorry`.
- Aeneas prints the char literal `'\''` as `'''`, which Lean cannot parse. Patch Funs.lean by hand and record the patch.
- `Str` is a semireducible `def` (`Slice U8`), so `simp [bind_tc_ok]` and `WP.spec_ok` silently fail to fire on `ok (s : Str)`. Use `set_option allowUnsafeReducibility true in attribute [local reducible] Aeneas.Std.Str` (the same holds for external types defined as `def`, e.g. HashMap := List). When simp still will not rewrite a `do let y ← ok x; …`, `exact (bind_tc_ok _ _).trans ?_` works.
- `f <$> ok x = ok (f x)`: `rw [← pure_tc_eq, map_pure]`.
- `step*` can time out on a `match b with | 32#uscalar => …` over a scalar literal. Use `let* ⟨o, ho⟩ ← spec`, then `rw [ho]` and `split`. In the "other" branch, recover `b ≠ 32#u8` with `UScalar.eq_of_val_eq`.
- `step*` leaves `sorry` (or metavariable goals) for loop-spec arguments it cannot infer, and for `core.option.Option.map` with a closure. Pass the arguments explicitly with `let*`, and `unfold core.option.Option.map` first.
- Full `simp` folds `l[j] :: l.drop (j+1)` back into `l.drop j`. Use `List.takeWhile_cons_of_pos/neg` with `rw`.
- External std functions can all be `def`s that state the contract, with no axioms. Examples: `&s[i..]` panics unless `is_char_boundary`; HashMap is an association list; Display/Hash are no-ops when only used for panic messages. `#print axioms` then shows only the three standard axioms.

## 2026-10-24 semver fork: proving Display/Debug and other std glue (Aeneas)
- Aeneas's `core.fmt.Formatter` is opaque and its `write_str` ignores the string ("simplistic model").
  A theorem "fmt writes X" proved against it is vacuous (it holds for any X). Fix used in semver: make
  the glue generic over a small private trait (`Sink { put_str, put_char, put_u64_debug }`) with one
  impl for `Formatter`. Proofs take an arbitrary Sink instance, so they pin down every call.
- Same for Hash: Aeneas's `Hasher` has only `write`/`finish`; leave std's `u64::hash`, `str::hash`
  as axioms and prove the exact call sequence.
- Exact formatter calls are observable (writers that fail partway or count calls). Record calls in the
  differential test with a `fmt::Write` that logs `write_str` and `write_char` separately. std's
  `PadAdapter` (used by `{:#?}`) adds one `write_str("    ")` per nesting level and drops empty writes.
- Aeneas bugs seen: the char literal `'\''` is printed as `'''` (Lean parse error); `u8 as char`
  gives "Unreachable". Use `char::from(39u8)` / `char::from(b)` (then model `From<u8> for char`).
- Keep the extraction honest: diff the set of `/-- [rust::path]` items in FunsExternal_Template.lean
  against the hand-kept FunsExternal.lean on every run, so a new std assumption fails the build.

## 2026-10-24 crc32fast: SIMD and multi-target lessons (Aeneas/Lean)
- `Result` binds are not definitional. A `rw_bind` macro (`first | rw [bind_ok] | rw [bind_tc_ok]`)
  plus `simp only [uncurry_apply_pair]` beats `simp` (which unfolds call_mut inside binders).
  `let (a,_) := (x,()); ok a` inside a bind needs `erw [bind_ok]`.
- Multi-line Lean struct literals: start fields on a new line, aligned, or you get
  "unexpected identifier; expected '}'".
- One build per target/feature set (riscv no_std, x86 no_std/std, aarch64 no_std/std). Keep shared
  proofs in common/ and put only Detect.lean, Variant.lean, kernels and FunsExternal per variant.
- Model facts outside the code's control (CPU feature flags, where align_to splits) as `opaque`
  values and prove for every value; do not pick one.
- Overflow that Aeneas reports as `fail` is often a real debug-build panic. Check with a tiny
  Rust program before calling it a spec assumption; crc32fast's Hasher had one.
- Loop helpers Charon cannot read (intrinsic loads, index loops over chunks) can be moved into
  small functions and marked `--opaque`, but then gate 1 needs an equivalence proof or a fork.

## 2026-10-24 Neovim (later): Frama-C lessons
- **Frama-C 33 WP soundness bug**: a `const char x[] = "..."` is assumed all zeros (default -wp-init-const). Goals can be vacuously proved. Rewrite such arrays to brace lists via a CBMC-proved tool patch. Details: toolchain-bugs/framac33-wp-string-init.md.
- **Never define the spec from the code's own tables** (e.g. `alphabet[...]` in a postcondition). Write the reference table into the ACSL as a logic function and prove the code table equals it; otherwise a changed table changes the spec too.
- **WP ignores allocation** (\fresh, frees). Track it with ghost variables in the stub (live count + last pointer; xfree requires p == last) so leaks, double frees and returning freed memory fail the proof.
- `(uint64_t)b << 56` reaches the prover as `to_uint64(lsl(b,56))`. State bit lemmas with the same casts (`(uint64_t)(b << 56)`) so they match the goal; check them with Z3 bit-vectors by mapping casts to masks.
- When a C value is a big expression, derive facts from a small logic value first (e.g. `be64(s + i)`), then transfer with one equality assert. Big let-bound terms make lemma instantiation time out.
- Differential test that's cheap and useful: compile the pristine file, the patched+annotated file and a glibc-byteorder build, and compare all three with a reference (Python's base64 + canonical check) on ~100k inputs.
- E-ACSL 33 fails on logic functions with `integer` parameters (GMP codegen bug); don't count on it for runtime spec checks.

## 2026-10-24 Aeneas: str::ends_with and friends, fn items (Helix text helpers thread)
- `str::ends_with/starts_with::<P>` (Pattern trait + `for<'a> ReverseSearcher<'a>` bound) crash Aeneas. Fix without touching
  source: charon `--exclude 'core::str::pattern'`, then the LLBC pass helix-verify/real-common/tools/specialize_fn.py, which
  points each call at a copy specialized to the concrete pattern type (ends_with_str, ends_with_char) with no trait clauses.
  Give each copy a Lean model and difftest it. Should work for strip_suffix, rfind, find, contains the same way.
- Fn items passed as closures (`iter.all(f)`) still fail ("Arrow types are not supported"); erase_fndef_binders.py
  gets call_mut through but not call_once. Needs an Aeneas OCaml fix (SymbolicToPureTypes: treat TFnDef as borrow-free) or a second tool.
- Make opaque third-party types `abbrev` (not `def`) when you model them with a Lean structure, so lemmas about the
  structure apply without unfolding.
- In Aeneas output, `do let x ← ok a; f x` simplifies with `bind_ok`, not `bind_tc_ok`.

## 2026-10-24 inih (Frama-C WP): why string facts vanish in big functions, and the fix

- Symptom: a fact that proves at once in a small copy (e.g. `valid_read_string(&section[0])`
  after a call that writes another buffer) times out in a large function, on every prover.
- Cause: WP's Qed simplifier deletes a hypothesis like `section[k] == '\0'` when it can
  derive it itself (through `memcpy(...)` memory terms). The SMT provers then lack the
  ground term `M[section + k]` they need to fire the strlen axioms, so they never start.
  Writing the hint as a quantifier does not help; Qed removes that too. `-wp-no-core`,
  `-wp-havoc`, `-wp-no-filter` and Wp.filter scripts did not help.
- Fix: wrap the facts in named predicates that Qed does not unfold, plus small lemmas
  (all proved by WP) linking them to strlen:
  `ini_nul_at(s,k)`, `ini_nonnul(s,n)`, `ini_str_len(s,n)`, with lemmas
  nul_at -> strlen <= k, str_len -> strlen == n, strlen -> str_len, shift, and frame
  lemmas. A frame lemma for `e + 1` needs its own form (`e[j + 1]`), because Qed
  rewrites `(e+1)[j]` to `e[j+1]` in goals but the prover won't match that with `shift(shift(e,1),j)`.
  Pattern per write: assert ini_nonnul before the write, a ghost label, then after the write:
  nul_at, a cell frame against the label, nonnul, str_len, then valid_read_string.
- Also: index-form facts (`\forall integer j; ... s[j]`) prove where pointer-quantified
  facts (`\forall char* p; s <= p < e ==> *p`) don't. Add an index-form ensures to helpers.
- Ghost labels work: `/*@ ghost L: ; */` then `\at(e, L)`.
- The Frama-C "const char a[] = \"..\" assumed zero" WP bug (toolchain-bugs/) also exists in 32.1.
- (cmdline, gates 7/8) A gate-8 test can set private fields when it is a `#[cfg(test)] #[path=...] mod gate8;` child of the module. That lets the Tokenizer start at unreachable positions, so panic agreement is tested too. Reuse the one helix copy: append the mod line, run, restore, and check the restore with `cmp`. Show that the harness discriminates with one-line sed mutants of the Rust source (run against the unchanged Lean extraction).
- An `#eval` of an Aeneas `Vec` needs `⟨slice⟩`, because `alloc.vec.Vec` is a structure wrapping a `Slice`. `Flag` clashes with Mathlib, so write `command_line.Flag.mk`. Field names like `alias` need «» in structure-instance notation.
- Hash no-op contracts can be justified by testing real std with a constant hasher (write no-op, finish 0) next to RandomState: the answers must agree.

## Helix parsers (snipparse)
- Parser-combinator code (helix-parsec: `impl Parser` closures nested by `seq!`/`choice!`) is out of reach of
  Charon/Aeneas fdebf20. Charon runs out of memory (it tries 12 GB allocations) on the nested closure types, and
  the small combinators fail in Aeneas: closures give "Can't end abstraction"; a `Peekable` loop gives "Joining
  region abstractions containing shared loans…". Check this before writing a model of combinator code.
- Mutually recursive model fns extract as one `partial_fixpoint` block. To prove them: state each fn's spec with a
  hypothesis `hm : ∀ k > i, ManySpec s k` for the recursive callee. Prove each fn from `hm`, using
  `apply WP.spec_bind (hm …)` at the call (or `step*` with the instantiated spec as a local `have`). Then close with
  strong induction on `len - i`. This is much simpler than a fixpoint-induction proof.
- The spec side can use WF `mutual` defs over `List Nat`, `termination_by (s.length, rank)`, with `match h : …` only
  for the decreasing proofs. Prove separate `_eq` unfolding lemmas that drop the `h :`, and use those in simp_all.
- PEG properties are cheap once the spec exists. For example: "parse fails iff input is empty" needs only "every
  alternative's rest is shorter" lemmas plus `Option` `or_some` / `bind_eq_some_iff` destructuring.
- Mutation-test the difftest itself (4–5 hand mutants of the model). It costs minutes and shows the generators
  actually reach dedup, `$0` and transform paths.
- Aeneas's `Result` is now a coinductive tree, not an inductive. To evaluate a model in a test
  program use `match Result.match r with | .ok v => ...`; `| ok v` patterns no longer work.
- Lean models of CPU instructions can be checked cheaply: a Rust program prints random cases from
  the real instruction, `lake env lean --run Check.lean` evaluates the model on them (270k cases in
  seconds). aarch64 runs under qemu-user-static with gcc-aarch64-linux-gnu as linker.
- In no_std builds crates often pick SIMD kernels with `cfg!(target_feature)`, so
  `RUSTFLAGS=-C target-feature=...` selects each kernel for differential tests.
- leanchecker on many heavy modules in one call can be OOM-killed (exit 137, empty log); run per module.

## 2026-10-24 Helix movement thread: Aeneas on real (unmodified) Rust, and what blocks it
- Charon handles real helix-core fine with `--start-from <fn path> --opaque ropey --opaque tree_house --opaque unicode_segmentation`; Aeneas then exits non-zero but still writes partial Lean (check for `sorry`, don't treat exit code as crash). Lean names are `module.fn`, not `module::fn`.
- Patched Aeneas (helix-verify/motion/aeneas-patches/, build.sh via Nix) adds non-ASCII char literals, string escapes and `match` on char. Upstream fdebf20 also mis-printed `'\''`, `'\\'` and Latin-1 chars (invalid UTF-8 in Funs.lean).
- Remaining hard blockers on idiomatic code (each more than a day in Aeneas): nested borrows (`x.chars_at(..).method(..)`), `&dyn Fn` closures, fn items passed as closures (late-bound regions), `iter().find(|..|)` lifetime constraints, loops with several exits (`?`/return inside an inner loop), and some "Unexpected error"s. Plan for a rewrite (fork) or another tool when code is iterator/closure heavy.
- Charon's `--start-from` builds leave a big incremental cache in target/: set CARGO_INCREMENTAL=0 (it filled 11 GB here). Saturn's test suite stalls a Nix OCaml build: disable its tests.

## Lessons from Helix editing helpers (2026-10-24)
- External type axioms show up in `#print axioms` as soon as a theorem mentions a struct containing them; give external types placeholder definitions instead of axioms.
- Make container models (e.g. List for HashSet) `@[reducible]`, or rewrites fail on type mismatches.
- Mutation scripts must check the failure is a proof error in a proof file, not a compile error or missing dependency.
- Rust >= 1.87 panics on `format!` widths above u16::MAX: grep for user-controlled widths.
- Aeneas: a local variable named like a crate shadows that crate's namespace in the generated Lean; qualify with `_root_`.
- Lean: when a translated function has a big repeated block, copy the block verbatim into a Lean `def` and state the larger spec with calls to it; `exact`/`WP.spec_mono` sees through the def by unfolding. Prove each `let acc ← if ... ` stage as its own small lemma and chain them with `let*`.
- Lean: `scalar_tac` loops on hypotheses like `x = btl t y` together with `heq : l = line`; clear them before arithmetic goals, or use omega.

## 2026-10-24 — globset model / difftest lessons (globset subagent)
- Read the real code path before modelling options: in globset 0.4.18 `literal_separator`, `empty_alternates`, `case_insensitive` are never read by the parser, so they cannot affect `build()` Ok/Err. A "drop the empty_alternates check" mutant only makes sense as "wrongly add one"; a mutant that only changes data the oracle doesn't observe (e.g. class ranges) is *equivalent* — label it as a control instead of counting it as missed.
- `GlobBuilder::build` never returns `ErrorKind::Regex`; `Glob::compile_matcher` `.expect`s and PANICS on regex-syntax `nest_limit` (250). Deeply nested `{…}` (from depth ~82 for `{a,b{a,b…}}`, 125 for `{a,{a,…}}`, 250 for `{{…a…}}`) in an `.editorconfig` section header crash Helix. Always difftest the follow-up call (`compile_matcher`) under `catch_unwind`, not just the fallible one.
- Lean `#eval` checkers over ~2M cases: interpreted speed ~7k cases/s. Avoid `let p ← get; …; set {p with arr := p.arr.push x}` — the extra reference forces an array copy per push (quadratic on long inputs); use `modify fun p => {p with arr := p.arr.modify i f}`. Don't keep a whole saved state across a loop for rollback; save only the fields Rust saves.
- Lean 4.35 String API: `String.trimRight` is gone and `String.take` returns `String.Slice` (no `Repr`); use `splitOn` / `String.ofList (s.toList.take n)`.
- Mutation testing without polluting the model: textual replacement (must occur exactly once) + concatenating the mutated model with the checker body (minus its `import`) into one file run by `lake env lean`.

## 2026-10-24 semver fork: serde, ledger, and local forks in vpipe
- Aeneas rejects serde's traits (`Serialize`/`Serializer`/`SerializeSeq`... are mutually recursive).
  Fix used in semver: keep serde.rs to one serde call per method, and move the logic (parse,
  error mapping, `expecting` text) into plain functions in the crate, generic over a small private
  trait (`DeError { from_parse_error }`) with a blanket `impl<E: serde::de::Error>` in serde.rs.
  Extract without the serde feature. The 13 adapters left are listed as trusted and differential-tested.
- Function ledger in Lean, not by grep: a `#ledger` command (semver lean/tools/Ledger.lean) walks
  the environment, and for each def from the extracted Funs module lists the theorems whose
  *statement* names it (abbrevs unfolded; `match_N` skipped; `f_loop`/`.body` count for `f`; a
  trait-impl record counts when all its members do). It found 7 real gaps a text search missed.
- Proving "a parse error never makes printing fail": carry `asciiTo s k` (every byte before k is
  ASCII) through each parser as an invariant on the result; at an error offset it gives a UTF-8
  char boundary on valid input, via `String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero`.
  The same invariant with end = length proves parsed identifiers are ASCII.
- `Str` is `Slice U8` but not reducible, so `simp`/`rw [bind_ok]` on `ok text` often fails.
  Use `WP.spec_bind (m := (ok text : Result (Slice U8))) (Pₘ := fun s => s = text)`.
- vpipe `upstream` can be a local fork as a git bundle (`git bundle create x.bundle --all`).
  A bare repo on /mnt/project-files fails with "dubious ownership". Delete a stale
  ~/vpipe-work/<lib>/src when the upstream URL changes: vpipe reuses an existing checkout.

## 2026-10-24 — helix uri.rs (Aeneas fdebf20 / Charon 0.1.293 / Lean 4.35)
- Aeneas "Unreachable" (InterpExpansion.ml:449) on `peekable.peek().copied()`: no flag helps; extract a source variant with the same loop minus the `peek`, reuse its loop verbatim, hand-write only the prologue, flag it in GATE1, and cover it by gate 8.
- `str::pattern::Pattern` stand-in: map each `trait_impl_id` separately (char vs &str); a blanket sed to `Pattern.char` silently mistypes `strip_prefix("//")`.
- Aeneas `Iterator` impl_defs carry `peekable :=`/`collect :=` fields the Lean lib lacks: delete them in postprocess.
- `Result` is coinductive: no `rfl`/`cases` on `ok a = ok b`; use `Std.bind_ok`, `Std.bind_tc_ok` (for `do (← …)` in lib defs), `Result.ok_injective`.
- Tuple-let `let (a, b) ← …` in extracted code: after the bind reduces, `simp`/`dsimp`/`split` cannot reduce `match (x, y) with …` (module-private matcher). Use `show <the branch you expect>` (defeq) or `change`; in own models write `r.1`/`r.2`.
- Loops: prove `f it r = do let x ← body it r; match x with | cont y => f y.1 y.2 | done z => ok z` by `rw [loop]; simp only [Std.bind_tc_eq]; congr 1; funext r; cases r <;> rfl`, then plain induction.
- Do not `simp` inside `mkStr l h`/Slice args (rewrites in the proof make terms ill-typed): state helper lemmas whose RHS builds the proof cleanly (`strip_prefix_ss`, `find_slash`, `index_upto_slash`) and `rw` them.
- `Str` vs `Slice U8` mismatches for lib lemmas (`Slice.len_val`, bind of `as_bytes`): give a type ascription `(x : Slice U8)` or a tiny bind lemma instead of `attribute [local reducible] Str` (avoids `allowUnsafeReducibility`).
- String literals: `strBytes "file://" = [...]` by `decide +kernel` (plain `decide` gets stuck).
- Grep Lean output for `error` not `error:` — tagged errors print as `error(lean.unknownIdentifier)`.

## 2026-10-24 inih (Frama-C WP): goals that are true but drown in context

- Symptom: a goal holds and a hand-trimmed copy proves in under a second, but the full
  goal times out on all provers, even at 300 s. Goal splitting (-wp-split) and Wp.filter did not help.
  Z3 random seeds flip it between proved and timeout, so it's search noise, not missing facts.
- Fix 1, lemmas: WP sends every *global* lemma to every goal. Put helper predicates
  and their lemmas inside an `axiomatic Name { ... }` block; WP then includes them only in
  goals that use those symbols. Three of our general string lemmas alone were enough
  to make an unrelated goal time out.
- Fix 2, custom strategy: a 50-line WP plugin (inih-work/prune/inih_prune.ml) registers
  `-wp-auto inih:prune`. For goals the provers fail, it makes a sub-goal with the same
  conclusion that keeps only Type/Init facts and universally quantified hypotheses
  (memory frames, call effects), and drops branches and plain facts. Sound by construction:
  it only removes hypotheses. Build: `ocamlfind ocamlopt -thread -shared -package frama-c-wp.core
  -o inih_prune.cmxs inih_prune.ml` inside the Frama-C image; load with `-load-module`.
  It is ~50 lines of trusted code; list it in CLAIM.md.
- String literals in a big loop: WP restates a literal's contents only on the loop-head
  memory. A frame assert right before the call helps the trimmed goal:
  `\forall char* p; base(p) not one of the local buffers ==> *p == \at(*p, Ltop)` with
  a ghost label `Ltop` at the top of the loop body.
- `void*` context pointers cast back to a struct need `-wp-model Typed+Cast`; plain Typed
  fails every goal touching the struct. Record the cast assumption in CLAIM.md.
- Several readers/modes: one annotated copy, a prelude with `#ifdef` modes that map the
  function-pointer call to the concrete callee, and a `reader == &callee` precondition so
  the call site has to prove the mode applies.

## 2026-10-24 Helix text helpers: contracts for third-party code must be difftested before use
- When a proof rests on a stated property (a contract structure) of a third-party crate, difftest that property against the
  real crate right away. Helix's grapheme boundary proofs assumed unicode-segmentation's GraphemeCursor gives the same
  answers on chunked text as on the whole string; a chunked-driver difftest showed 1.13.3 violates it (regional indicators
  counted twice at a chunk cut), which made the proofs vacuous for the real crate. See helix-verify/text/useg/fix/.
- Extracting the real third-party crate (here unicode-segmentation with Aeneas) beats a hand model: the extracted cursor
  matched the crate on 18k whole-string queries with no model to write.

## 2026-10-24 Creusot 0.14.0 + pinned Why3: install that works (percent-encoding Creusot thread)
Needs a cloud environment with full network access (gitlab.inria.fr, git.frama-c.com, opam.ocaml.org). Steps (about 25 min, mostly OCaml builds):
```
apt-get install -y opam libgmp-dev pkg-config m4
opam init -y --disable-sandboxing --bare
git clone https://github.com/creusot-rs/creusot.git && cd creusot && git checkout v0.14.0   # 65349025c67e
# skip why3-ide: it needs GTK dev packages and nothing here uses the IDE
OPAMVAR_in_creusot_ci=true OPAMYES=1 ./INSTALL
```
`./INSTALL` builds the opam switch at ~/.local/share/creusot (OCaml 5.3.0, why3 git-05bf4ddf, why3find git-0f054b93), downloads the pinned solvers (Alt-Ergo 2.6.4, Z3 5.1.0, CVC4 1.8, CVC5 1.4.1) and installs `cargo creusot` for Rust nightly-2026-08-03. `cargo creusot version` prints "bad CVC5 version" because it misreads CVC5's multi-line banner; harmless. Project setup: add `creusot-std = "0.14.0"` to [dependencies], run `cargo creusot init` (writes why3find.json), then `cargo creusot` (translate + prove) or `cargo creusot <pattern>` to prove only matching files.
Pitfalls on real (unmodified) crates:
- `use creusot_std::prelude::*` makes derive(Clone)/derive(PartialEq) ambiguous. Import `{*, Clone}` explicitly (Creusot's Clone derive has the same field-wise body plus `ensures(result == *self)`) and `core::cmp::PartialEq` for std's derive; Creusot still wants a `DeepModel` impl for types with derived PartialEq.
- creusot-std already has an empty extern spec for `Formatter::write_str`; a crate cannot add a second one ("duplicate extern specification"). To give it a contract, vendor creusot-std and delete that one entry (`[patch.crates-io] creusot-std = { path = "vendor/creusot-std" }`).
- Public consts that build a struct with private fields fail with "Cannot make ... transparent"; `#[cfg_attr(creusot, trusted)]` on the const makes it opaque (adds no assumption).
- Statics like a `&[u8; 768]` byte table are unsupported ("Unsupported constant value").
- `&x as *const T` is translated as a fresh pointer with unknown address, so `ptr::eq` of two pointers made from references can never be proved.
- Std functions with no contract (is_ascii, array `[..]` index, split_first, to_digit, from_utf8_unchecked on &[u8], from_utf8_lossy, Iter::any, slice to_owned...) give "impossible precondition" warnings; add `extern_spec!` contracts and difftest each one against real std.

## uri.rs round 2 (patched Aeneas + shared HelixReal models), 2026-10-24
- Patched Aeneas (b43126bd build 4) still hits `Unreachable` (Interp.ml:682) on `peekable.peek().copied()` when the copied value is kept across `next()`; repro in helix-verify/aeneas-repro/uri-peek/. Keep the `sorry` as printed and mark dependents blocked.
- `#eval` refuses any expression that depends on `sorry`, transitively: gate-8 harnesses must skip (and count as blocked) every case reaching a sorry'd function, even branches that would not call it at runtime.
- HelixReal.StdModelsBase defines `core.result.Result.ok`; inside `namespace core.result.Result` an unqualified `ok` then resolves to it. Write `Std.Result.ok` in local models there.
- TestUtil helper named `bytesOf` clashes with `StdModel.bytesOf` (ambiguous under `open StdModel`); rename local helpers.
- A planted bug in the shared `isCharBoundary` (accept 0xBF) passed a 240k-case std difftest: random strings rarely put a continuation byte at the probed index. Add a dedicated boundary difftest (strings built from 2/3/4-byte chars incl. U+00BF, check `get(..i)`/`get(i..)` for every i); 20k cases catch it.
- Porting proofs to the shared Pattern models: one bridging lemma `core.str.Str.find pi s c = <old findBytes match>` (via `findPat_single`) let the round-1 proofs go through almost unchanged.
- Audit Aeneas external model signatures before trusting real-code output: `Cell::set` is modelled as `Cell T → T → Result Unit`, which silently drops the write. Check FunsExternal_Template.lean for models that lose effects, and keep the template (it has axioms) out of the build.
- "Translates" is not "usable": check for transitive sorry (a function that calls a sorry'd one).
- Partial Aeneas output can still give real-code proofs: copy the needed declarations verbatim into a standalone file, give stand-ins only to external types the functions never inspect, and check the copy mechanically.
- Cheap mutation testing: copy the project, symlink .lake/packages, copy .lake/build, apply one edit to Funs.lean per mutant (40-150 s each). Report survivors for unproved properties.
- `lake build` has no -j; use LEAN_NUM_THREADS=2 to limit memory.
- Aeneas "Can't end abstraction ... owns the static region" on real code comes from `log` macros ('static metadata). Stubbing the log crate's macros to `{}` fixes it; list it as a trusted-base change.
- Make extracted externals `opaque` instead of `axiom` (give Result an Inhabited instance); real-code theorems then take external behaviour as explicit hypotheses and #print axioms stays clean.
- Parameter/field names equal to a namespace (selection, transaction, syntax, regex) break elaboration of generated Lean; rename or `_root_`-qualify.
- Aeneas IntoIter is a Vec with a real next, so loops over into_iter() are directly provable.

## command_line.rs round 3 (patched Charon/Aeneas, real-code Lean proofs), 2026-10-24
- `-filter-trait-methods` (patched Aeneas) was what unblocked functions using `take_while`/`count` and `impl Iterator for X` (`parse_percent_token`, `Tokenizer::next`).
- Aeneas build 8 refuses some `&'a self` methods that build 2 accepted: "Unimplemented: reborrowing a shared value which contains borrows living in the region of its own loan" (e.g. `self.signature.flags.iter().any(..)` inside a `debug_assert!` of `get_flag(&'a self, ..)`). Diff your extraction after every toolchain bump; a proof on old output may lose its function.
- Literals that come out of `split` on an extracted `match` look like `40#8#uscalar` and are not reducibly equal to `40#u8`. Bridge with `(rw [hle]; decide)` / `fun e => h (by rw [e]; decide)`, and reduce reference-model ifs with `simp (config := { decide := true }) only [...]`.
- `refine WP.spec_bind (thm args ?_ ?_) ?_` unifies the callee with the goal first and leaves the preconditions for later; better than `step with` when preconditions mention literals.
- `Result` is an irreducible ITree: `rfl` does not compute binds. Use `simp only [bind_ok, bind_tc_ok, uncurry]`; for `let (a, b) := (x, y); ok ..` use `apply (WP.spec_ok _).2`. Plain `dsimp only` there unfolds the WP into `∀ a ∈ Set.range ..`.
- Contracts that return a struct/tuple state (e.g. `TakeWhile` as a triple) make simp produce type-incorrect terms. Wrap the constructor in a named def (`HV.tw it p f`) and simp with it.
- Do not put a `match` on the postcondition inside a lemma statement: it becomes a different matcher from the one in the goal (mismatch or timeout). Generalize the post as `P` with `hP : ∀ y, Q y → P (.done y)`.
- `cases h : t.validate` substitutes into struct literals and breaks unification with later call-site specs; use `by_cases` with `rw [if_pos h]`/`rw [if_neg h]`.
- omega does not see through `{ t with pos := i }.pos`; restate the goal with `show i.val ≤ ...`.
- Restate a callee's spec at the call site's shape (`pq_at`, `pb_at` via `WP.spec_mono`) once, and the many delimiter cases close with one `all_goals (...)` script.
- Tokenizer theorems need `SliceValid` (every boundary-to-boundary slice is valid UTF-8, true for any `&str`) because `push_str` contracts fail on invalid UTF-8; and an `i32` nesting counter forces `len + 2 < i32::MAX`.
- (command_line, build 13) Aeneas build 13 + Charon build 6 emit real bodies for library fn items used as closures (`.map(AsRef::as_ref)`); delete any hand-written stand-in for such `...Insts.CoreOpsFunctionFnOnce...` instances and rebuild. In command_line the proofs went through unchanged, and build 12 restored `get_flag` (`&'a self`), which build 8 had refused.

## globset/regex compile-failure model (GlobSetBuilder::build Err), 2026-10-24
- Read real limits with a binary search: rebuild the regex with `nest_limit(k)` / `nfa_size_limit(Some(k))` and search for the smallest k that succeeds. That gives the exact AST depth and NFA memory_usage for each case, so the difftest compares internal numbers and not only Ok/Err. It caught mutants that a pass/fail comparison missed.
- Feature unification in the real dependency graph changes behaviour: Helix enables regex-automata's `hybrid`, so meta::Regex also builds a reverse NFA under the same size limit, and for some globs (`{é,ü}^n`) only the reverse NFA goes over. Pin the exact feature set of the real Cargo.lock in the difftest crate.
- Lean models over large inputs (300 KB globs): `l ++ [x]` in loops, `chars.length` recomputed per sub-parse, and literal-merge appends made the checker quadratic (hours). Keep accumulators reversed and pass fuel down instead of recomputing lengths.
- Mutation runner: strip `theorem` blocks from the scratch copy, otherwise mutants that only break a proof show up as "build failed" instead of being tested.
- Look for equivalent mutants. A hash-map eviction mutant was equivalent until it was redesigned; one renumbering-only mutant (S10) is still uncaught because state IDs only show through FNV slot collisions. Report such survivors and do not count them as caught.
- `GlobBuilder::build` recurses on brace nesting (to_regex and Token drop) and overflows the stack at around 13k nested `{` on a 2 MiB thread stack (release build). Any input-controlled glob needs a nesting guard before globset is called.

## inih: build options and heap mode in WP (2026-10-24)
- Annotations are preprocessed, but you can't add `#if` lines to the code without breaking the "stripped copy == upstream" check. Use variadic macros in the prelude instead: `#define INI_IF_ML(...) CAT(INI_IF_ML_, INI_ALLOW_MULTILINE)(__VA_ARGS__)` with `_1` = the args and `_0` = nothing. This works for terms, conjuncts and set members (a leading comma inside the args is fine).
- Behavior-specific loop invariants (`for b: loop invariant`) are not enough for RTE goals, because RTE goals are proved for every behavior. Write general invariants guarded by `\at(cond, Pre) ==> ...` instead.
- WP can't use Frama-C libc's malloc/realloc/free: `\fresh`/`\freeable` show up as "Degenerated" goals.
- **Pitfall (made my heap proofs vacuous, caught 2026-10-24):** do NOT write freshness as a postcondition like `\forall p; \at(\valid_read(p), Pre) ==> \separated(\result.., p)`. WP's validity table is the same before and after a call, so the result block itself is "valid at Pre" and the clause yields a contradiction. Every goal after the call then proves trivially. Signs: suspiciously fast proofs, and an RTE goal you know is false proving. What works: an uninterpreted predicate marking allocated cells (put it in the assigns clauses), and an `admit` of separation from the specific local objects right after each successful allocation. Always run a vacuity check (-wp-smoke-tests or a planted bug) after adding any assumed contract.

- Aeneas lean (build 13): `do` binds tuples via Std.uncurry, so simp needs uncurry_apply_pair. A Bind-typeclass congruence lemma unified against Std.bind ran out of memory; use Std.bind lemmas and rewrite one side with a helper lemma instead of rewriting under binders. (Helix editing helpers)
- Mutation checks on Aeneas b13 output: Lake may not rebuild modules importing Funs*.lean when only a function body changes, so a mutant can look "missed" while old builds are reused. Delete dependent build outputs (.lake/build/lib/.../*.olean for importers) before each mutant. (Helix editing helpers)
- Aeneas 14 rejects index_mut on a fixed-size array inside a loop. Keep Vec in the refactor and relate it to the upstream array with a toVec lemma. (Helix editing helpers)
- Non-vacuity: for every R-cond/M theorem with hypotheses, build a concrete instance that satisfies all of them and derive one concrete consequence. doc_formatter found a hypothesis (g.char_idx < f g for all usize) that no instance could meet, which made a whole layer of theorems vacuous; mutation checks did not catch it. (Helix editing helpers)
- Publish scripts must never rm -rf a shared folder before copying: if the local source was cleaned up, the shared copy is lost. Copy first, or skip when the source is missing. (Helix editing helpers)
- (command_line non-vacuity) `SliceValid`-style "∀ a b, ... → (String.fromUTF8? ..).isSome" is not decidable as stated; prove it from a bounded Bool checker (`checkSV l = true → SliceValid l`) and close the checker with `decide +kernel` on the concrete bytes. Lean 4.35 reduces `String.fromUTF8?`, `toStr`, well-founded `stopFrom` and the extracted-free reference models under `decide +kernel` in seconds. For Hoare-triple theorems, the concrete consequence is `WP.spec_mono (thm ...)` to a postcondition with numbers, plus `WP.spec_exists` when an explicit witness value is wanted. `deriving instance DecidableEq for` the model/extracted enums in the witness file only.

- (semver non-vacuity, 2026-10-26) Finding which theorems need instances: a Lean meta script that lists theorems
  with explicit Prop binders that no other theorem's proof term uses (semver lean/tools/Conditional.lean). Skip
  generated names (mvcgen_spec, congr_simp, eq_N, hcongr_N). Lemmas used inside other proofs have their hypotheses
  met at the use site, so only the unused ones need a witness file. `decide` closes `¬ IsValidUTF8` on concrete
  ByteArrays; well-founded parser mirrors need `rw [loopDef]` unfolding, not `decide`/`rfl`; reuse a round-trip
  theorem (print_parse) to get a concrete parse result instead of evaluating the parser.
- Never declare an external type as Unit (Aeneas TypesExternal placeholders) when hypotheses talk about its values: every value becomes equal, and hypotheses like "slice s has chars CH s" force empty text. Use opaque types. Also bound every index in hypotheses about functions that panic out of range; "for all i" makes them unsatisfiable by real data. (Helix editing helpers)

## inih: non-vacuity witnesses for C contracts (2026-10-26)
For the "concrete instance" rule with Frama-C/WP, two cheap checks per configuration:
- `-wp-smoke-tests` on every proved function: WP tries to prove `false` at each precondition set and each block; any success means dead code or contradictory preconditions. Smoke goals reported "Valid" in `-report` mean the smoke test passed (code is live).
- A witness file that `#include`s the annotated source and adds (a) bodies for every abstract function (reader, handler, allocator), proved against their contracts, so each contract can be met; (b) one concrete call per entry point on fixed inputs, with an `assert` of one consequence. WP proves the call's preconditions, which is the concrete instance. Fill test buffers cell by cell (the string-initializer bug).
- Abstract predicates with no definition (like a heap marker) get a concrete definition under a witness-only `#ifdef`, which shows the axiom-free declaration is consistent.
- Pitfall: `\valid(q)` inside an assigns set is evaluated in a separate allocation table that has no `linked` hypothesis, so it is unprovable there. Keep validity out of assigns sets.
- E-ACSL 32.1 crashes on quantifiers inside predicate bodies and on `\at(e, Pre)` with quantified indices, and skips labels in loop invariants. It is not usable for runtime-checking annotations of this style without rewriting them.

## 2026-10-26 inih: WP cache keeps timeouts
- With `-wp-cache update`, a prover timeout is stored in the cache. A later run reports it as "(Cached)" Timeout and never retries. When a goal times out under machine load, rerun it with `-wp-cache none` (or a longer timeout) before treating it as unproved.

## 2026-11-01 inih: Frama-C's fgets contract has no length bound
- Frama-C 32.1's libc spec for `fgets(s, size, f)` says only that the result is NULL or `s`, and that `s` is then a valid string. It does not say the string is shorter than `size` (C11 7.21.7.2p2 guarantees that). With a heap buffer WP cannot find the bound, so goals such as `strlen(line) < max_line` time out.
- Fix used for inih: an `admit ensures` on the fgets wrapper that states the C11 bound, listed as a trust assumption.

## CBMC vs Frama-C WP for C byte code (Neovim thread, 2026-11-02)
- WP's typed memory model keeps `char` and `uint8_t` reads of the same bytes separate; code that casts `char *` to `uint8_t *` needs tool patches. CBMC is bit-precise and has no such issue.
- For functions with bounded loops, CBMC + `--unwinding-assertions` + nondeterministic inputs is a complete proof. Use exact-size malloc objects so any out-of-bounds read fails the pointer check, and a 6-byte object to cover longer strings.
- CBMC 6.4 lets malloc fail by default: pass `--no-malloc-may-fail`. Run with and without `--unsigned-char`.
- `(int)` of a pointer difference or a size is the most common bug found so far.

## 2026-11-02 Aeneas soundness: third-party interior mutability is not refused (parsers thread, probe14)
The patched toolchain's interior-mutability check (toolchain README item 13) matches types by path (core::cell,
core::sync::atomic, std::sync). Third-party types holding an `UnsafeCell` (e.g. parking_lot / lock_api `Mutex::lock`)
are translated as pure functions of `&self`: a write through the guard is dropped and the next `lock()` reads the old
value. Proofs about such code prove the wrong thing. Repro: helix-verify/probe14/repros/third_party_interior_mut/.
Rule until the tool detects UnsafeCell structurally: check every extracted crate for third-party Mutex/RwLock/Cell-like
types reached through `&self` (grep the LLBC/Funs for lock_api, parking_lot, once_cell, arc_swap) and refuse claims that
depend on them. Builds 13/14 and stock all accept it.

## 2026-11-02 semver: serde traits, Unicode tables, big const arrays in Aeneas (Lean)
- serde's `Serialize` and `Serializer` refer to each other through generic methods. In Lean that is a
  structure in a negative position of its own fields, so Aeneas warns "will not type-check" and it can't be
  fixed by ordering or `mutual`. Charon `--exclude`/`--opaque` do not drop required trait methods. What works:
  a vpipe postprocess that drops the Serializer-family fields taking `T: Serialize` (code that only calls
  `collect_str` never needs them; any real serializer still fits the trimmed structure) and reorders
  Serialize* -> Serializer -> Serialize. See pipeline/libraries/semver/tools/serde_traits.py. The de side
  needs nothing: unused provided Visitor methods are skipped by Charon.
- `--features serde` goes in vpipe.toml `cargo_args`. Aeneas uses `F32`/`F64` with no definition: define them
  in TypesExternal (abbrev to Lean Float32/Float) when they only appear in unused trait methods.
- std `char` Debug (Unicode tables) can't be translated. Generate a range table from std with a small Rust
  program, write the lookup in translatable code, and test every scalar value against std and upstream.
  Proofs about the 1812-entry const array: Aeneas needs `-max-recdepth 65536`; prove table facts with
  `decide +kernel` and `set_option maxRecDepth 100000 in`; avoid `simp` with the array in context.
- Exhaustive char tests take minutes in debug builds: `#[cfg_attr(debug_assertions, ignore)]` and run them
  in the release cross-check.

## 2026-11-02 Charon build 6 (default MIR level): match guards over enum fields can extract as `fail panic` (parsers thread, fmt17)
With `--preset=aeneas` at the default MIR level, Charon keeps the fake shallow borrows of match-guard places; a borrow
through an enum downcast becomes undefined behaviour, which Aeneas turns into `fail .panic`. The extracted function then
panics where Rust does not (seen: helix command_line ParseArgsError Display, arm `max: None, min > 0, actual < min`).
A proof that "the code panics" there is WRONG about Rust. Fix: extract with `--mir elaborated`. Every thread using
Charon build 6: re-extract with `--mir elaborated` and diff Funs.lean; any difference is a suspect arm. Evidence:
helix-verify/fmt17/extract-default-mir-cmd/ and fmt17/STATUS.md "Toolchain bug found".
Follow-up (parsers audit, helix-verify/miraudit/REPORT.md): `--mir elaborated` is not a free switch. For helix
command_line get_flag/has_flag it makes Aeneas 13/14 refuse the body ("reborrowing a shared value ...", sorry). Use it
for fmt/Display extractions, otherwise diff the two extractions and keep the default where they agree.
Update 2026-11-02 02:27Z (Aeneas thread): both issues above are fixed in Charon build 7 + Aeneas build 17
(toolchain README items 28, 29, 31; regression cases guard_fake_borrow, third_party_interior_mut). Charon drops MIR
fake borrows, and third-party opaque types that can reach an UnsafeCell are refused when passed by & to a bodiless
library function.

Frama-C WP lessons (Neovim thread, 2026-11-02): (1) Typed model puts offset arithmetic in
index-quantifier triggers, so Z3/CVC5 fail even `forall i<m. s[i]!=0 ==> s[j+1]!=0`; quantify
over pointers instead and run CVC5 with --full-saturate-quant (neovim_verifier tools/bin/cvc5-fsq).
(2) `\block_length - \offset` variants are unprovable (abstract offset table); use a ghost length
parameter. (3) Induction over recursive logic functions needs ghost lemma functions with loops.
(4) -wp-cache none when retrying, the cache keeps timeouts. Alt-Ergo is unfree in nixpkgs, not used.

## 2026-11-02 Match-guard `fail panic` affects every patched Charon build, not only build 6 (Helix movement thread)
- fmt17's ParseArgsError positive control gives 2 wrong `fail panic` arms at default MIR on patched Charon builds 2, 5 and 6 (and 0 with `--mir elaborated`); stock Charon gives 0. So re-audit extractions made with ANY patched build, not just build 6.
- `--mir elaborated` can lose loop bodies ("Continue to outer loops are not supported yet") on code with labelled continue; diff both and keep the default where no arm differs.
- Check what a toolchain dir really holds by binary sha256 against the README tarballs; a dir named for build 8 here held Charon build 2 + Aeneas build 4. Scripts: helix-verify/motion/miraudit/scripts/.

## 2026-11-02 Charon default-MIR match-guard bug: wider than build 6; how to audit (editing-helpers thread)
- The spurious bare `| none => fail panic` arm appears at the default MIR level in EVERY patched Charon build 1-6 (tested on a crate shaped like ParseArgsError::fmt). Default level gives the same LLBC as `--mir promoted`. Stock vpipe Charon is clean at both levels.
- `--mir elaborated` is not a drop-in replacement: Aeneas leaves `sorry` on some functions (e.g. ChangeSet::{retain,delete}, comment transaction builders), and charon-driver OOMs (~14 GB) on helix ChangeSet::compose. Better: extract at both levels and compare the panic arms one by one; keep the default extraction when the arms match.
- Find UnsafeCell-holding types structurally: LLBC `marker_traits.is_freeze == false` (a lower bound; Charon sometimes leaves it empty).
- Agents share the session scratchpad: use unique scratch directory names (two audits collided on `scratchpad/mir/`).
- Editing-helpers result: no suspect arm in any extraction; no claim affected. Details: helix-verify/helpers/vacuity/MIR_AUDIT.md.

## 2026-11-02 Creusot 0.14 on Helix code (Creusot parsers thread, helix-verify/creusot-parsers/)
What Creusot 0.14.0 cannot do. Each item was checked with a small repro:
- `#[ensures]` on a fn returning `impl Trait` fails: the macro puts the type in a closure parameter. Callers see an opaque type, and the trait-level `Deref`/`DerefMut` specs are `requires(false)`. So code that derefs a returned `impl DerefMut` (fuzzy `lock`) can't be verified.
- `static` items: "unsupported definition kind ... Static". Fn item to fn pointer coercion: "Unsupported pointer cast ... ReifyFnPointer". Calling a fn-pointer *field* works, given a type invariant `self.f.precondition(())` (`#[logic(open(self))]`).
- Calling `dyn Fn` gives "forbidden dyn type". Unsizing into `Box<dyn Error>` works. serde derive output uses `&dyn de::Expected`, so derived Deserialize can't be translated.
- Logic can't recurse through `Seq`/`Vec` (Seq is not positive, and logic mutual recursion is forbidden), so no specs over trees. Program mutual recursion is always rejected.
- Pearlite has no string literals. Use `const X: &str` with `X.deep_model()`. Note that `str::to_owned` gives `result@ == self@` (view), while `==` on str and `HashMap::get` keys use `deep_model`. These are distinct in Why3, so pick the matching one.
- Missing from creusot-std 0.14: `Result::map`/`map_err`, `String::new`, `&A == &B`, `str::parse`. See normalize-uri/src/std_extra.rs and ec_std.rs.
- For-loop ghost names: `produced`, `__creusot_for_iter` (current) and `__creusot_for_iter_old` (initial) work in invariants and in body `proof_assert!`. After the loop, `__creusot_for_iter` is gone, so carry facts in invariants. Facts that hold only on the `break` path still reach the code after the loop.
- The project mount can't hold symlinks ("Function not implemented"). Point `[patch]` paths at a real vendor copy.

## 2026-11-02 Kani loop contracts for any input length (percent-encoding thread)
- `-Z loop-contracts` with `kani::arbitrary::any_slice_ref_unbounded()` / `any_vec_unbounded()` ran out of memory (14 GB) even on a 3-line loop. Fix: `-Z unstable-options --cbmc-args --object-bits 8` (or 10). Then it proves in seconds. `--cbmc-args` must be last on the command line (it eats the rest, e.g. `--harness`).
- With unbounded lengths add `kani::assume(len <= 1 << 40)`; otherwise CBMC reports spurious "Offset result address must equal original pointer address plus offset" failures.
- Needs `#![cfg_attr(kani, feature(stmt_expr_attributes, proc_macro_hygiene))]`. `while let` works. `for` loops only take invariants over Kani-known iterators (Vec, slices).
- A harness needs `#[kani::unwind(2)]` or more for loops with contracts. If any unwinding assertion fails, Kani marks every other result UNDETERMINED.
- To give a std loop an invariant: generate a byte-for-byte copy of the std function from rust-lang/rust sources at the toolchain's commit (`rustc -vV` commit-hash, raw.githubusercontent.com), add only the invariant line, and `#[kani::stub]` the std function with it. Example: percent-encoding-creusot/bundle/kani/scripts/gen_std_copy.py.
- Always run a must-fail control harness and a `kani::cover!` for the branch the assertion sits in.

## 2026-11-02 Ghost position labels on external values can be unsatisfiable (editing-helpers thread)
A hypothesis like "there is a label sr : RopeSlice -> Nat×Nat with sr (byte_slice a b) = (a,b)" is false for ropey: Light slices store no position, so byte_slice(0..0) and byte_slice(1..1) are the same value. Any theorem assuming it is vacuous on ordinary documents. Label by content (e.g. the slice's chars) instead, and check every label hypothesis against a concrete instance with two equal-content slices. Proof: helix-verify/helpers/ropey_bridge/lean/RopeyBridge/LabelVacuity.lean.

## 2026-11-02 inih: WP hides pointer differences between a local array and a pointer
- In WP's default Typed model, `start - &line[0]` (start a char pointer, line a local array) and the length of a callee's `assigns s[0 .. end - s - 1]` show up as "Hide sub-term definition / Uncomparable locations" in the goal. The fact is then simply missing, and simple goals time out.
- `-wp-model Typed+raw` (no reference-variable optimisation) keeps them. Check a stuck goal with `-wp-gen -wp-print` and grep for "Hide sub-term" before adding hints.
- Also: `assigns { *p | char* p; base(p) == base(s) && s <= p < end }` frames worse than `assigns s[0 .. end - s - 1]`.

## 2026-11-02 Reproducible builds: record the patched Aeneas in the lakefile (editing-helpers thread)
Two independent reviewers could not build our published projects with stock ~/hv-shared/packages: they silently need a patched Aeneas Lean library (build16 patch, or the pk16 copy). Every published project must say in its lakefile or a setup script which patch it needs, and its STATUS build line must match. Reviewers should build from the published copy, not the author's tree.
