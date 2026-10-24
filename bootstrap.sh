#!/usr/bin/env bash
# Bring a fresh container from nothing to a working, self-tested pipeline.
#   bash /mnt/project-files/pipeline/bootstrap.sh [lean|framac|all]
# Steps: install the `vpipe` command, install pinned toolchains, run the protected gate.
set -euo pipefail
P=$(cd "$(dirname "$0")" && pwd)
VH=${VPIPE_HOME:-$HOME/.vpipe}
mkdir -p "$VH/bin"
# The project-files mount is noexec, so the command lives locally and calls python3 on the script.
printf '#!/usr/bin/env bash\nexec python3 %s/bin/vpipe.py "$@"\n' "$P" > "$VH/bin/vpipe"
chmod +x "$VH/bin/vpipe"
grep -q '.vpipe/bin' "$HOME/.bashrc" 2>/dev/null || echo 'export PATH="$HOME/.vpipe/bin:$HOME/.vpipe/aeneas:$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"
export PATH="$VH/bin:$PATH"
vpipe setup "${1:-all}"
python3 "$P/self/gate.py"
echo "bootstrap done: run 'vpipe --help'"
