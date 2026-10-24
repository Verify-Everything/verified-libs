
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
