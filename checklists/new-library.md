# Taking on a new library

1. **Fit.** Widely used (downloads or dependents), small to medium (roughly under 5k lines in the
   part you verify), no public verification attempt (search papers, GitHub, Zulip, the tool's
   showcase lists). Record the search in the manifest's comment.
2. **Tool.** Rust: Lean via Aeneas. C: Frama-C WP (no dependable C-to-Lean path yet). Other
   languages: add a tool template first (`vpipe improve --goal "support <tool>"`).
3. **Pin.** Pick a release tag and its commit hash.
4. **Scaffold.** `vpipe new <lib> --lang rust|c --upstream <git url> --commit <sha> --version <tag>`.
5. **Extract first, spec later.** `vpipe run <lib>` once with empty proofs. For Rust, look at the
   Aeneas warnings and Charon errors before writing any spec: unsupported features decide scope.
   Known fixes: SIMD/arch code -> riscv64 no_std target (see manifest comment); missing std
   models -> leave the function out or model it.
6. **Scope.** Fill `[scope].properties` with 2-5 statements that matter to users (round trip,
   no overflow, matches a reference, no out-of-bounds). Fill `[scope].exclusions` honestly.
7. **Prove.** By hand in the thread, or `vpipe run <lib> --agent` to let an agent iterate.
8. **Report.** `results/SUMMARY.md` updates on every run. Write status to
   verification-notes/<lib>.md and cross-library lessons to verification-notes/general.md.
9. **Feed back.** If something was done by hand that the next library will also need, add it to
   `self/BACKLOG.md` or run `vpipe improve`.

**Finished means every function.** A library is done only when every function in the pinned upstream
source is verified or has a verified fix (results/SUMMARY.md shows Functions N/N). Unsupported or
cfg-excluded functions stay open until they are handled (model crate, patch, or a different tool).
Map model-crate functions to their theorems in libraries/<lib>/functions.toml.
