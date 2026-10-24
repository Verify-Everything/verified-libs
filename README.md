<p align="center">
  <img src=".github/assets/verified-libs-mark.svg" alt="verified-libs: a package cube with the Verify Everything seal" width="140">
</p>

<h1 align="center">verified-libs</h1>

<p align="center"><b>The libraries that made it. Receipts included.</b></p>

---

**verified-libs** is a registry of machine-checked libraries. Every entry comes with:

- the **specification** it was verified against,
- the **proof** (or verification harnesses),
- a **pipeline** that re-checks the proof from scratch with a pinned toolchain, and
- a **claim card** (`CLAIM.md`) stating exactly what is proven, under which tool, at what strength, what is trusted without proof, and what is *not* covered.

Any language, any verifier. The rule is that the claim is precise and anyone can re-check it.

## Status

**No entries yet.** The standards are in draft and the first entry is in progress. Watch the repo or open an issue if you'd like to submit one.

## What "verified" means here

"Verified" means *machine-checked against a stated formal specification*. It does not mean supply-chain attestation ("built from source", "signed"), and it never means "bug-free". Each entry carries a **strength level**:

| Level | Meaning |
|---|---|
| `functional` | Full functional correctness: behaviour proven against a complete specification. |
| `contracts` | Pre/postconditions proven for the public API. |
| `safety` | Absence of undefined behaviour / runtime errors proven, without bounds. |
| `bounded` | Bounded model checking or bounded proofs: correct up to stated bounds. |

The details are in [STANDARDS.md](STANDARDS.md).

## Layout

```
libs/
  <library>/
    <version>/
      CLAIM.md     # the claim card: what is and isn't proven
      spec/        # the formal specification
      proof/       # proofs or verification harnesses
      pipeline/    # run.sh + pinned toolchain that re-checks everything
templates/
  CLAIM.md         # start here
```

CI checks that every entry follows this layout and that its claim card is complete.

## Contributing

Start with [CONTRIBUTING.md](CONTRIBUTING.md). In short: open a **Submit a library** issue, copy `templates/CLAIM.md`, and open a PR with the entry.

## Prior work

We stand on others' shoulders: [verify-rust-std](https://github.com/model-checking/verify-rust-std), the Isabelle [Archive of Formal Proofs](https://www.isa-afp.org/), [mathlib](https://github.com/leanprover-community/mathlib4), [Verus](https://github.com/verus-lang), and the Verified Software Repository proposed under the Verified Software Grand Challenge. verified-libs aims to be cross-tool and cross-language, with every claim labelled and re-checked.

## License

To be decided before the first entry lands. Each entry also keeps the license of the library it verifies.

---

<sub>Part of <a href="https://github.com/Verify-Everything">Verify Everything</a>. ∀x. verified(x).</sub>
