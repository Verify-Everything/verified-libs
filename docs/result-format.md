# Result format

`results/<lib>/<timestamp>.json` per run; `latest.json` is the newest. `vkit report`
builds `SUMMARY.md` from every `latest.json`.

Top-level keys (from a real crc32fast run):
- `library`, `commit`, `version`, `tool`, `started`, `finished`, `pipeline_version`
- `toolchain`: installed versions (`aeneas`, `charon_rust`, `lean`, ...)
- `source`: applied `patches`, upstream/differential `tests` and their outcome
- `extract` (Rust): `ok`, `stage`, `aeneas_rc`, `postprocess`, `unsupported` (items Aeneas
  skipped), `assumed_axioms` (std models left as axioms), `external_template_changes`, `warnings`
- `prove`: `ok`, `seconds`, `theorems` (per theorem: status and axioms), `proved`, `total`,
  `sorries`, `axiom_thms` (theorems resting on non-standard axioms), `unaudited`, `errors`;
  for Frama-C a per-function proved/total table
- `functions`: the every-function inventory. `total`, `verified`, `fixed`, `open`, `complete`
  (true only at N/N), `functions` (one entry per function in the pinned upstream source with its
  status and evidence or reason), `overrides_not_found` (ids in `functions.toml` that matched
  nothing)

The engine owns the exact schema; if this page and the engine disagree, the engine wins. Open
an issue so the page gets fixed.
