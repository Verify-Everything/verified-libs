<p align="center">
  <img src=".github/assets/verified-libs-mark.svg" alt="verified-libs: a package cube with the Verify Everything seal" width="140">
</p>

<h1 align="center">verified-libs</h1>

<p align="center"><b>The libraries that made it. Receipts included.</b></p>

---

**verified-libs** is a registry of machine-checked libraries, plus the toolkit to add more. Every
entry comes with the **specification** it was verified against, the **proof**, a **pipeline** that
re-checks it from scratch with a pinned toolchain, and a **claim card** (`CLAIM.md`) stating exactly
what is proven, at what strength, what is trusted without proof, and what is not covered.

```bash
curl -fsSL https://raw.githubusercontent.com/Verify-Everything/verified-libs/main/install.sh | bash
```

## What "verified" means here

**Verified** means: the exact upstream source at a pinned commit (or a published fork with proved
fixes) is proved, by a recorded tool, to meet a formal specification for all inputs, with every
assumption listed. It does not mean built from source, scanned, fuzzed or tested, and it never
means "bug-free".

Admission is strict, because this is meant to hold up against attackers who use AI to find bugs:
ten gates, no waivers ([STANDARDS.md](STANDARDS.md)). Every function, feature and target of the
real code at full functional correctness; spec and success criteria approved before work starts;
at least 10 planted bugs caught; a clean trusted base; reproducible CI; and two independent
reviews. Anything weaker is published as a **candidate**, never as verified.

| Label | Meaning | Admits |
|---|---|---|
| `full-correctness` | meets a functional spec for all inputs; no UB, panic or crash | yes |
| `safety-contracts` | memory/bounds pre/postconditions only | no |
| `no-ub` | free of undefined behaviour only | no |
| `bounded` | up to a stated size or loop bound | no |
| `tested` | differential or property tests only | no |

## Status

**No verified entries yet.** Three candidates are in progress (live numbers in
[results/SUMMARY.md](results/SUMMARY.md)):

| Candidate | Version | Tool | Headline properties proved | Theorems | Functions at full-correctness |
|---|---|---|---|---|---|
| [crc32fast](libraries/crc32fast/) | 1.5.3 | Lean (Aeneas) | slow, 16-byte and combine paths equal the reference CRC-32; incremental = one-shot | 132/132 | 9/43 |
| [percent-encoding](libraries/percent-encoding/) | 2.3.2 | Lean (Aeneas) | encoder, decoder and round trip match a reference spec | 49/49 | 9/26 |
| [semver](libraries/semver/) | 1.0.28 | Lean (model crate) | version order is a lawful total order; parse never panics; parse/print round trips | 145/145 | 4/92 |

semver's proofs are about a model crate, which counts only once model-to-code equivalence is proved.

## Layout

```
libs/<library>/<version>/        admitted entries: CLAIM.md, spec/, proof/, pipeline/
candidates/<library>/<version>/  same shape, below the bar (created as entries move over)
libraries/<lib>/                 vpipe engine working area: manifests and proofs in progress
templates/CLAIM.md               start here
bin/ toolchain/ self/ selftest/  the vpipe engine (re-checks everything, improves itself)
skills/                          agent skills (also a Claude Code plugin)
docs/                            installation, adding a library, trust model, engine
```

## Quick start

### 1. Install
```bash
curl -fsSL https://raw.githubusercontent.com/Verify-Everything/verified-libs/main/install.sh | bash
# or, from a fork you cloned:
git clone https://github.com/<you>/verified-libs && cd verified-libs && bash install.sh
```
The installer shows its plan and asks before changing anything. It installs the `vkit` and
`vpipe` commands into `~/.vpipe/bin`, copies the agent skills into your agent's skills folder,
and (if you choose) installs the pinned provers. Flags: `--agents claude,codex|none`,
`--tools lean,framac,cbmc|all|none`, `--yes`, `--dry-run`.

Claude Code users can install the skills as a plugin instead:
```
/plugin marketplace add Verify-Everything/verified-libs
/plugin install verify-everything@verify-everything
```

Linux (x86_64, aarch64) runs everything natively. On macOS or Windows, open the repo in the
[dev container](.devcontainer/) (VS Code, Codespaces, or `devcontainer up`).

### 2. Check
```bash
vkit doctor          # tools, pinned versions, mathlib cache, network, skills
vkit selftest        # engine self-test on small fixtures
```

### 3. Verify something
Ask your agent:
```text
Use the verify-library skill to pick a small, widely used Rust crate and verify it in Lean.
```
Or by hand:
```bash
vkit new <lib> --lang rust --upstream <git url> --commit <sha> --version <tag>
vkit run <lib> --extract-only    # what Aeneas can translate; decides the scope
vkit run <lib>                   # build proofs, audit axioms, write results
vkit run <lib> --agent           # let a headless Claude session write specs and proofs
```

## How it works

```
upstream @ pinned commit ─► extract (Charon+Aeneas → Lean)  ─► your specs + proofs ─► lake build ─► axiom audit ─► results/<lib>/latest.json
                         └► C: CBMC harnesses (bounded) ─► Frama-C WP + ACSL (unbounded) ─────────────────────► results/<lib>/latest.json
```
- **Pins.** Every library is pinned to a commit; every tool to a version in
  [`toolchain/versions.toml`](toolchain/versions.toml). Results record both.
- **Trust.** A Lean theorem counts as proved only if it rests on Lean's three standard axioms.
  `sorry`, extra `axiom`s, `native_decide` and `bv_decide` are reported, not hidden. Std
  functions Aeneas can't translate are modelled by hand and listed as assumptions.
- **Re-checking.** `vkit run-all` re-runs every library; CI runs it on a schedule so a new
  upstream release or tool version shows up as a diff in `results/`.
- **Self-improving engine.** `vpipe improve` lets an agent change the engine itself; a protected
  gate (`self/gate.py` + fixtures) decides keep or roll back. See [docs/engine.md](docs/engine.md).

## Skills

| Skill | Use it to |
|---|---|
| [verify-library](skills/verify-library/SKILL.md) | run the whole workflow: pin, scaffold, scope, prove, report |
| [pick-verification-target](skills/pick-verification-target/SKILL.md) | choose a library and check for prior verification |
| [lean-aeneas-proofs](skills/lean-aeneas-proofs/SKILL.md) | write Lean specs and proofs over Aeneas output |
| [framac-wp-proofs](skills/framac-wp-proofs/SKILL.md) | prove C with ACSL and Frama-C WP |
| [cbmc-bounded-checks](skills/cbmc-bounded-checks/SKILL.md) | bounded checks and mutation tests for C |
| [verification-setup](skills/verification-setup/SKILL.md) | install and repair the toolchain |
| [submit-verification-results](skills/submit-verification-results/SKILL.md) | open a PR with honest, reproducible claims |
| [review-verification-claim](skills/review-verification-claim/SKILL.md) | adversarially review an entry and pick the planted bugs (never your own) |

## Contributing

Start with [CONTRIBUTING.md](CONTRIBUTING.md); agents read [AGENTS.md](AGENTS.md). In short: open a
**Submit a library** issue with your success criteria, wait for approval, then verify and open a PR.
Lessons from every library so far: [notes/general.md](notes/general.md).

## Documentation
- [Installation](docs/installation.md): platforms, restricted networks, dev container
- [Adding a library](docs/adding-a-library.md): the full checklist
- [Standards](STANDARDS.md): the ten gates, labels, forbidden constructs, lifecycle
- [Trust model](docs/trust-model.md) and [result format](docs/result-format.md)
- [Engine](docs/engine.md) and [pipeline design](docs/pipeline-design.md)

## Prior work

We stand on others' shoulders: [verify-rust-std](https://github.com/model-checking/verify-rust-std), the Isabelle [Archive of Formal Proofs](https://www.isa-afp.org/), [mathlib](https://github.com/leanprover-community/mathlib4), [Verus](https://github.com/verus-lang), and the Verified Software Repository proposed under the Verified Software Grand Challenge. verified-libs aims to be cross-tool and cross-language, with every claim labelled and re-checked.

## License

To be decided before the first entry lands. Each entry also keeps the license of the library it verifies.

---

<sub>Part of <a href="https://github.com/Verify-Everything">Verify Everything</a>. ∀x. verified(x).</sub>
