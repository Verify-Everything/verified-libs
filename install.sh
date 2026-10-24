#!/usr/bin/env bash
{
# Truncation guard (same idea as REA's installer): everything sits inside this brace group, so a
# `curl | bash` download cut off early is a syntax error and runs nothing.
set -euo pipefail

REPO_URL="${VKIT_REPO:-https://github.com/Verify-Everything/verified-libs.git}"
DEST="${VKIT_DIR:-$HOME/verified-libs}"
VH="${VPIPE_HOME:-$HOME/.vpipe}"
agents="" tools="" yes=false dry=false path_edit=true

usage() {
  cat <<'EOF'
Usage: install.sh [--agents claude,codex,gemini|none] [--tools lean,framac,cbmc|all|none]
                  [--dir PATH] [--yes] [--dry-run] [--no-path]

Installs the verification toolkit:
  1. clones the repo (or uses the checkout this script is in)
  2. puts `vkit` and `vpipe` in ~/.vpipe/bin and adds that to PATH
  3. copies the agent skills into your agents' skills folders
     (Claude Code: ~/.claude/skills; Codex and Gemini CLI: ~/.agents/skills)
  4. optionally installs the pinned provers (`vkit setup`)
It prints the plan and asks before changing anything. Nothing is installed system-wide
except what you approve in step 4 (rustup, zstd, CBMC .deb, Nix packages).
EOF
}

while (($#)); do
  case $1 in
    --agents) agents=$2; shift 2 ;;
    --tools) tools=$2; shift 2 ;;
    --dir) DEST=$2; shift 2 ;;
    --yes|-y) yes=true; shift ;;
    --dry-run) dry=true; shift ;;
    --no-path) path_edit=false; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option $1" >&2; usage >&2; exit 2 ;;
  esac
done

fail() { echo "install failed: $*" >&2; exit 1; }
command -v git >/dev/null || fail "git is required"
command -v python3 >/dev/null || fail "python3 (3.11+) is required"
python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))' || fail "python3 is older than 3.11"

# Use this checkout if the script runs from one.
here=""
if [ -n "${BASH_SOURCE[0]:-}" ] && [ -f "$(dirname "${BASH_SOURCE[0]}")/bin/vkit.py" ]; then
  here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
  DEST=$here
fi

ask() {  # ask "question" default(y|n)
  $yes && return 0
  [ -t 0 ] || [ -e /dev/tty ] || return 1
  local a; read -r -p "$1 " a </dev/tty || return 1
  [[ ${a:-$2} =~ ^[Yy] ]]
}

# Pick agents: detected ones are offered, not assumed.
if [ -z "$agents" ]; then
  det=()
  { command -v claude >/dev/null || [ -d "$HOME/.claude" ]; } && det+=(claude)
  { command -v codex >/dev/null || [ -d "$HOME/.codex" ]; } && det+=(codex)
  { command -v gemini >/dev/null || [ -d "$HOME/.gemini" ]; } && det+=(gemini)
  if $yes; then agents=$(IFS=,; echo "${det[*]:-none}")
  elif [ ${#det[@]} -gt 0 ]; then
    read -r -p "Install skills for which agents? [${det[*]// /,}] (or none) " a </dev/tty || a=""
    agents=${a:-$(IFS=,; echo "${det[*]}")}
  else agents=none; fi
fi
if [ -z "$tools" ]; then
  if $yes; then tools=none
  else read -r -p "Install provers now? lean,framac,cbmc | all | none [none] " a </dev/tty || a=""; tools=${a:-none}; fi
fi
[ "$tools" = all ] && tools=lean,framac,cbmc

rc="$HOME/.bashrc"; [ "${SHELL##*/}" = zsh ] && rc="$HOME/.zshrc"
echo
echo "Plan:"
[ -z "$here" ] && echo "  - git clone $REPO_URL $DEST"
echo "  - write launchers $VH/bin/vkit and $VH/bin/vpipe"
$path_edit && ! grep -qs '.vpipe/bin' "$rc" && echo "  - add $VH/bin, ~/.elan/bin to PATH in $rc"
[ "$agents" != none ] && echo "  - install skills for: $agents (existing folders of the same name are backed up)"
[ "$tools" != none ] && echo "  - vkit setup for: $tools (each step shows its own plan and asks again)"
$dry && { echo "(dry run: nothing changed)"; exit 0; }
ask "Proceed? [y/N]" n || { echo "Cancelled; nothing changed."; exit 1; }

if [ -z "$here" ]; then
  if [ -d "$DEST/.git" ]; then git -C "$DEST" pull --ff-only; else git clone --depth 50 "$REPO_URL" "$DEST"; fi
fi
mkdir -p "$VH/bin"
# Launchers call python3 on the scripts, so the checkout may sit on a noexec mount.
printf '#!/usr/bin/env bash\nexec python3 %q "$@"\n' "$DEST/bin/vkit.py" > "$VH/bin/vkit"
printf '#!/usr/bin/env bash\nexec python3 %q "$@"\n' "$DEST/bin/vpipe.py" > "$VH/bin/vpipe"
chmod +x "$VH/bin/vkit" "$VH/bin/vpipe"
if $path_edit && ! grep -qs '.vpipe/bin' "$rc"; then
  echo 'export PATH="$HOME/.vpipe/bin:$HOME/.vpipe/aeneas:$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"' >> "$rc"
fi
export PATH="$VH/bin:$PATH"

if [ "$agents" != none ]; then
  args=(); IFS=, read -ra al <<< "$agents"; for a in "${al[@]}"; do args+=(--agent "$a"); done
  vkit skills install "${args[@]}" --yes
fi
if [ "$tools" != none ]; then
  IFS=, read -ra tl <<< "$tools"
  for t in "${tl[@]}"; do if $yes; then vkit setup "$t" --yes; else vkit setup "$t"; fi; done
fi
echo
echo "Done. Open a new shell (or: export PATH=\"$VH/bin:\$PATH\"), then run: vkit doctor"
[ "$agents" != none ] && echo "Restart your agent so it loads the new skills."
exit 0
}
