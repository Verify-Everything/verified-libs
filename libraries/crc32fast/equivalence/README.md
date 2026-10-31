# Gate 1: patch 0002 does not change behaviour

The Lean proofs cover the crate *after* `../patches/0002-simd-readable-by-aeneas.patch`, which
exists only so Aeneas can read the SIMD kernels. Gate 1 requires such a patch to be proved
equivalent to the original. The original here is the pinned upstream plus `0001` (the proved
overflow fix); `0002` changes two files:

| File | Change | Evidence | Result |
|---|---|---|---|
| `src/specialized/aarch64.rs` | `calculate`: `align_to` moved into `split_quads`; the `chunks_exact(4)` + `zip` loops written as index loops | Creusot proof (`aarch64/`) | proved, spec `calc_ok` |
| `src/specialized/aarch64.rs` | `crc_quads`: `for chunk in &mut quad_iter` written as `while let Some(chunk) = quad_iter.next()` | Creusot proof (`aarch64/`) | proved, spec `!fold_d(!crc, quads)` |
| `src/specialized/pclmulqdq.rs` | the unaligned loads in `get`, `get256`, `get512`, `reduce_128_to_crc` moved into `#[inline]` helpers `load128/256/512` | identical x86_64 assembly (`x86_asm.sh`) | identical in 8/8 builds |

Run everything: `bash equivalence/run.sh <pinned upstream checkout>`. It
0. builds `orig` (upstream + 0001) and `patched` (+ 0002) and checks 0002 touches only those two files,
1. runs `x86_asm.sh`,
2. checks with `check_verbatim.py` that every body marked `// verbatim:` in `aarch64/src/lib.rs`
   equals the `orig` (or `patched`) source once proof annotations are removed (only
   `#[invariant]`, `#[variant]` and single-statement ghost `snapshot!`/`proof_assert!` lines may
   differ; copied from `libraries/percent-encoding/creusot/`),
3. checks the SHA-256 of `creusot-std-0.14.0.crate` and applies `creusot-std-chunks.patch`,
4. translates `aarch64/` with Creusot 0.14.0 and proves every Why3 file with why3find
   (alt-ergo, z3, cvc5, cvc4), one file at a time with a wall-clock cap.

## aarch64: Creusot proof
`aarch64/src/lib.rs` holds the original and patched bodies of `calculate` and `crc_quads` (and
the patched `split_quads`), copied verbatim. Each pair is proved to meet one exact spec:
- `crc_quads`: `result == !fold_d(!crc, quads)`, where `fold_d` applies the `crc32d`
  instruction to each word in order.
- `calculate`: `calc_ok(crc, data, result)`, which says `result` equals one expression of `crc`
  and how `align_to` splits `data` (the three-way split and `combine` above 192 words, a single
  chain below). Since the spec is `result == <expression>`, both versions return the same value
  for every input.

Every loop has a `#[variant]`, so these are total-correctness proofs: both versions terminate,
and neither can panic (indexing, overflow of `n3 * 8`, `i + 4`).

## x86: identical assembly
Creusot cannot prove the x86 half. The change moves `_mm_loadu_si128(a.as_ptr() as *const _)` into
a helper, and Creusot 0.14 gives no contract to `<[T]>::as_ptr`, so it cannot show that two
calls return the same address. Instead, `x86_asm.sh` compiles both trees for
`x86_64-unknown-linux-gnu` with `--release` and compares the assembly. It covers `std` and
`no_std`, with and without the `nightly` feature, and with debug assertions on and off: 8 builds,
identical except for `.file`/`.loc`/`.ident` lines (source paths and line numbers). The
assembly contains `calculate`, `calculate_avx2`, `calculate_avx512` and `reduce_128_to_crc`.
Two planted changes to the helpers (a load one byte later, a 512-bit load that reads 32 bytes)
both change the assembly.

This is a different kind of evidence from a proof: it shows that rustc emits the same machine code
for both versions at `opt-level=3` (checked with stable rustc 1.97.0; the script prints the version
it ran with, and rustc is not pinned in `toolchain/versions.toml` for this). It relies on the compiler, which every
source-level proof here already trusts, and it is not checked at `opt-level=0`, where the helpers
are not inlined (the code still means the same; only the check does not cover it).

## Trusted base added by this check
- **T1** `__crc32d` is a deterministic function of its two arguments (its meaning is proved in
  Lean and cross-checked under qemu by `crosscheck/models.sh`).
- **T2** `crc_bytes` and `combine` (unchanged by 0002) are deterministic functions of their
  arguments (proved in Lean: `crc_bytes_eq`, `combine_eq`).
- **T3** std contracts, as documented: `<[T]>::align_to` returns a prefix, whole `U`s and a
  suffix whose sizes add up to the input. Where it splits depends on the address, which
  Creusot's `&[T]` does not carry, so the split is an opaque function of the slice, applied to
  the same `data` in both versions. The Lean model does the same (`a64.splitPre/splitMid`, and
  its proofs hold for every split). Also `<slice::Iter as Iterator>::fold` (calls `f` on each item
  in order, threading the accumulator; stated for closures whose state a call leaves unchanged).
- **T4** `creusot-std-chunks.patch`: a model of `slice::ChunksExact` (the chunks still to come and
  the remainder), with contracts for `<[T]>::chunks_exact` (chunk `i` is `s[i*n .. i*n+n]`, there
  are `len / n` of them, the remainder is the rest) and `ChunksExact::remainder`, as documented.
  Creusot takes a dependency's laws as axioms, so the two iterator laws the patch adds
  (`produces_refl`, `produces_trans`) are proved again in `aarch64/src/lib.rs`
  (`chunks_refl`, `chunks_trans`). The patch also gives `Zip` the drop rule creusot-std already
  gives `Chain`, `Enumerate`, `Map` and the other adapters: dropping a `Zip` drops both inner
  iterators (`resolve(zip) = resolve(a) && resolve(b)`, with the same `#[trusted]` coherence
  law as theirs). creusot-std 0.14.0 leaves `Zip`'s drop opaque, so after the original
  `for .. in (&mut chunks_a).zip(&mut chunks_b).zip(&mut chunks_c)` loop Creusot did not know
  that `chunks_b` and `chunks_c` keep their remainders. That is why the proof failed without it
  (checked).
- Creusot 0.14.0 and its `creusot-std` specs, Why3 and the four SMT solvers; for x86, rustc.

## Not yet done
- The engine (`vpipe`) does not run this check, so CI does not re-check it and gate 1 in
  `CLAIM.md` still reads "tool-only patches without a proved equivalence". For Lean entries the
  engine only accepts Lean theorems (`[patches].equivalence_theorems`). Counting this evidence
  needs Creusot pinned in `toolchain/versions.toml`, a selftest, and gate 1 taught to read it:
  an engine PR, separate from this library, and the same one percent-encoding is waiting for.
- Whether identical assembly is enough for gate 1 is the maintainer's call; the standard says
  "proved equivalent".
