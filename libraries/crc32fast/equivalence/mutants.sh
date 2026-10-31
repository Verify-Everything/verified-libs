#!/usr/bin/env bash
# Planted bugs for the aarch64 Creusot proof: each edit to an original or patched body (or a wrong
# loop variant) must make some proof goal fail. Run after run.sh, on its work folder:
#
#   bash equivalence/mutants.sh WORK_DIR        (WORK_DIR/aarch64 is the translated, patched crate)
#
# Exit 0 only if every mutant is rejected.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
WORK="$(cd "${1:-${VPIPE_WORK:-$HOME/vpipe-work}/crc32fast/equivalence}" && pwd)"
CAP="${CREUSOT_FILE_TIMEOUT:-600}"
export PATH="$HOME/.local/share/creusot/bin:$PATH"
export DUNE_DIR_LOCATIONS="why3find:lib:$HOME/.local/share/creusot/share/why3find"
export WHY3CONFIG="$HOME/.local/share/creusot/creusot_why3.conf"
M="$WORK/mutant"
bad=0; n=0

# mutant NAME MODULE FUNCTION FROM TO: replace FROM (once) inside `pub mod MODULE`.
mutant() {
  local name="$1" mod="$2" fn="$3" from="$4" to="$5"
  n=$((n + 1))
  rm -rf "$M"; cp -r "$WORK/aarch64" "$M"; rm -rf "$M/verif" "$M/target"
  if ! python3 -I - "$M/src/lib.rs" "$mod" "$from" "$to" <<'PY'
import sys
p, mod, f, t = sys.argv[1:]
s = open(p).read()
i = s.index(f"pub mod {mod} {{")
j = s.find("\npub mod ", i + 1)
j = len(s) if j < 0 else j
part = s[i:j]
if part.count(f) != 1:
    sys.exit(f"pattern occurs {part.count(f)} times in mod {mod}")
open(p, "w").write(s[:i] + part.replace(f, t) + s[j:])
PY
  then echo "ERROR $name: pattern"; bad=1; return; fi
  if ! ( cd "$M" && CARGO_INCREMENTAL=0 timeout 900 cargo creusot --dry-run-why3find >/dev/null 2>&1 ); then
    echo "ok   $name: rejected (does not translate)"; return
  fi
  local f="verif/crc32fast_creusot_aarch64_rlib/$mod/$fn.coma" out
  out=$(cd "$M" && timeout "$CAP" why3find prove -j 4 --no-autodetect-provers -t 10s "$f" 2>&1); local rc=$?
  if [ $rc = 0 ] && ! grep -q "✘" <<<"$out"; then echo "BAD  $name: proof still passes"; bad=1
  elif [ $rc = 124 ]; then echo "ok   $name: rejected (not proved within ${CAP}s, the cap run.sh uses)"
  else echo "ok   $name: rejected (goal failed)"; fi
}

# original crc_quads
mutant "orig crc_quads: chunk[3] -> chunk[4]" orig crc_quads "c = arch::__crc32d(c, chunk[3]);" "c = arch::__crc32d(c, chunk[4]);"
mutant "orig crc_quads: fold starts at !c" orig crc_quads ".fold(c, |acc, &q|" ".fold(!c, |acc, &q|"
mutant "orig crc_quads: result not inverted" orig crc_quads "        !c
    }" "        c
    }"
# original calculate
mutant "orig calculate: c1 starts at !1" orig calculate "let mut c1 = !0u32;" "let mut c1 = !1u32;"
mutant "orig calculate: stream b reads qc" orig calculate "c1 = arch::__crc32d(c1, qb[k]);" "c1 = arch::__crc32d(c1, qc[k]);"
mutant "orig calculate: 3 of 4 words per chunk" orig calculate "for k in 0..4 {" "for k in 0..3 {"
mutant "orig calculate: remainder of c reads qb" orig calculate "c2 = arch::__crc32d(c2, qc);" "c2 = arch::__crc32d(c2, qb);"
mutant "orig calculate: leftover from 2*n3" orig calculate "r = crc_quads(r, &quads[3 * n3..]);" "r = crc_quads(r, &quads[2 * n3..]);"
mutant "orig calculate: >= becomes >" orig calculate "if quads.len() >= MIN_TRIPLE_QUADS {" "if quads.len() > MIN_TRIPLE_QUADS {"
mutant "orig calculate: prefix bytes use post_quad" orig calculate "r = crc_bytes(r, pre_quad);" "r = crc_bytes(r, post_quad);"
# patched calculate
mutant "patched calculate: i += 3" patched calculate "i += 4;" "i += 3;"
mutant "patched calculate: remainder of a reads b" patched calculate "c0 = arch::__crc32d(c0, a[i]);" "c0 = arch::__crc32d(c0, b[i]);"
mutant "patched calculate: second combine uses c1" patched calculate "r = crate::combine::combine(r, !c2, block_len);" "r = crate::combine::combine(r, !c1, block_len);"
mutant "patched calculate: block_len n3 * 4" patched calculate "let block_len = (n3 * 8) as u64;" "let block_len = (n3 * 4) as u64;"
# patched crc_quads
mutant "patched crc_quads: chunk[7] -> chunk[6]" patched crc_quads "c = arch::__crc32d(c, chunk[7]);" "c = arch::__crc32d(c, chunk[6]);"
mutant "patched crc_quads: starts at crc" patched crc_quads "let mut c = !crc;" "let mut c = crc;"
# a wrong loop variant must be rejected (otherwise loops would only be partially correct)
mutant "orig calculate: wrong variant on the 0..4 loop" orig calculate "#[variant(4 - produced.len())]" "#[variant(produced.len())]"

rm -rf "$M"
[ "$bad" = 0 ] && echo "== $n/$n planted bugs rejected" || { echo "== planted bugs: FAILED"; exit 1; }
