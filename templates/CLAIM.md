---
library: example-lib            # upstream name
version: 1.2.3                  # exact version or commit verified
source: https://example.com/example-lib
tool: Lean 4                    # verifier used
tool_version: 4.x.y
strength: contracts             # functional | contracts | safety | bounded
status: verified                # verified | in-progress | broken
---

# Claim card: example-lib 1.2.3

## In one sentence

<!-- What a careful reader may now believe about this library, and nothing more. -->

## Properties proven

| Property (plain words) | Formal spec | Level |
|---|---|---|
| | `spec/...` | |

## Trusted base

<!-- Axioms, assumptions, unverified dependencies, unsafe/FFI boundaries, environment models, the checker itself. -->

## Not covered

<!-- Mandatory. What this proof does NOT say. "Nothing" is not an acceptable answer. -->

## Bounds (only for `bounded`)

<!-- Loop unwinding, input sizes, etc. -->

## How to re-check

```bash
./pipeline/run.sh
```

## Credits

<!-- Who did the verification work, as they wish to be credited (handles are fine). -->
