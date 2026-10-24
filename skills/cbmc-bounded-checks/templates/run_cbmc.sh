#!/usr/bin/env bash
# One CBMC proof for one harness at one exact input length.
# Exit 0 = no property violated, 10 = a property failed (CBMC's code), anything else = setup error.
#   bash run_cbmc.sh <upstream.c> <harness.c> <len> [extra cbmc args]
# Unwind = 2*len+10 covers loops that walk the input once or twice; raise it if
# --unwinding-assertions fails. --conversion-check is off: it flags (char)(128..255),
# which is implementation-defined, not UB.
set -u
SRC=$1; H=$2; L=$3; shift 3
HERE=$(cd "$(dirname "$0")" && pwd)
command -v cbmc >/dev/null || { echo "cbmc not found (vkit setup cbmc)" >&2; exit 2; }
exec cbmc --function harness -I "$HERE/stubs" -I "$(dirname "$H")" \
  --bounds-check --pointer-check --memory-leak-check \
  --signed-overflow-check --unsigned-overflow-check --pointer-overflow-check \
  --undefined-shift-check --div-by-zero-check \
  --unwinding-assertions --unwind $(( L * 2 + 10 )) -DEXACT_LEN="$L" "$@" "$H" "$SRC"
