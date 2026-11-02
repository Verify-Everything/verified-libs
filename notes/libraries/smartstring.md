# smartstring 1.0.1 (Helix's Tendril) — tracker

Entry: smartstring-verify/ (shared folder). Scope: smartstring-verify/SCOPE.md (what Helix uses).
Asked by Yerin (2026-10-24): verify the used parts of ropey, smartstring, smallvec as separate entries.

## Success criteria (written before proofs, 2026-10-25)
- Real code: the crates.io 1.0.1 archive (sha256 3fb72c63...), unchanged except proof code added under
  cfg(kani) / ghost annotations; build.rs output as on Helix's stable rustc (no `has_allocator`).
- Mode: LazyCompact only (the only one Helix uses).
- Every function in SCOPE.md proved for full functional correctness against the model
  "a SmartString is its byte string `as_str()`" (std String semantics), with no undefined behaviour
  (Kani memory-safety checks) and the right panics; representation invariant kept (inline iff
  discriminant bit set; inline len <= 23; boxed: cap >= 46, len <= cap, pointer even).
- Size assumption: every length and capacity <= 2^40 bytes (Kani's pointer model). To state in CLAIM.md.
- Loops over caller iterators (Extend, FromIterator): Creusot on the real code, using the Kani-proved
  push/push_str contracts (listed as cross-tool contracts in CLAIM.md).

## Plan / tools
- Kani 0.68 (CBMC 6.11): symbolic lengths, arbitrary contents, "for all i" checked at an arbitrary i.
  Prototype: boxed push_str proved for all lengths <= 2^40 in 5 s (2026-10-25).
- Creusot 0.14: Extend<&str>, Extend<char>, Extend<String>, FromIterator<char/&str/String>.

## Status
- Scope found (2026-10-25).
- In progress: Kani harnesses (~/smartstring/kani/proofs.rs, copy in smartstring-verify/kani/).
