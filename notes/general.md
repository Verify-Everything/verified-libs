
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
