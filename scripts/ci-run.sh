#!/usr/bin/env bash
# CI body of the verify job: engine gate, then each library or entry given, then the summary.
# Runs the same natively and inside the pinned toolchain container (container/Dockerfile).
#   bash scripts/ci-run.sh [lib | name/version ...]
# Plain names are libraries/<lib>/ working folders; name/version are candidates/ or libs/
# entries, which run --clean (admission gate 9 compares clean runs).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 self/gate.py --full
fail=0
for l in "$@"; do
  case $l in
    */*) python3 bin/vpipe.py run "$l" --clean || fail=1 ;;
    *)   [ -f "libraries/$l/vpipe.toml" ] || continue
         python3 bin/vpipe.py run "$l" || fail=1 ;;
  esac
  rm -rf "${VPIPE_WORK:-$HOME/vpipe-work}/${l%%/*}"   # keep runner disk free
done
python3 bin/vpipe.py report
exit $fail
