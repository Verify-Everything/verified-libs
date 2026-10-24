# Getting every function through the tools (fixes that worked)

Nothing here makes a function "out of scope". Each fix gets a skipped function into a form
the tools can verify, and each one is recorded (patch file, model mapping, or assumption).

Rust / Charon / Aeneas
- SIMD or arch-specific code: building for `--target riscv64gc-unknown-none-elf
  --no-default-features` (with `sysroot_default = true`) gets the portable path through Aeneas
  (crc32fast). That proves the portable path only: the SIMD paths stay open and need a second
  tool or target before admission.
- `alloc`/`std` features pull in Cow/String/Vec models: `--no-default-features` gets the no_std
  core through first, but every feature must be covered before admission.
- "Early returns inside of loops are not supported": a tool-friendly patch can rewrite `for ... { if p { return } }` as a
  `while i < len && !p(s[i]) { i += 1 }` search followed by the shared tail (percent-encoding). The patch must then be proved equivalent to
  the original for the entry to count; a differential test alone leaves it a candidate.
- Closures like `opt.map(|x| ...)`: rewrite to `match`.
- `impl Display` over a cloned iterator, derived `Debug` on structs holding `slice::Iter`:
  extraction fails. Rewrite in a patch (index loop instead of cloned iterator) or model the
  function in a model crate; until then it stays open.
- Large crates whose real code Aeneas can't take: a model crate (semver, Helix) is useful for
  finding the spec, but it counts only with a proof that model and real code behave the same,
  or if the model ships as a fork users adopt. For `unsafe` code, use a second tool that reads it
  (Verus, unbounded Kani, VeriFast) and link the proofs.
- Missing std models come out as axioms in `FunsExternal_Template.lean`. Copy to
  `<Module>/External/FunsExternal.lean` and replace the ones you use with definitions. Each is a
  trusted assumption: list it in CLAIM.md's Trusted base with a differential test against real std.

C / Frama-C / CBMC
- Compile the upstream `.c` unmodified; stub internal headers in a `stubs/` include dir.
- Model "malloc never fails" with `__CPROVER_assume(p != NULL)` (CBMC) or a requires clause (WP).
- Function pointers: redirect calls with a `-include` prelude macro to an abstract function
  with a contract covering every allowed implementation. (inih)
