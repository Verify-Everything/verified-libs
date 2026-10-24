#!/usr/bin/env python3
"""Protected acceptance gate for self-changes. The improve loop cannot edit this file or selftest/.
It runs the (possibly changed) vpipe CLI on fixed fixtures and compares with selftest/expected.json."""
import json, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
exp = json.loads((ROOT / "selftest/expected.json").read_text())
full = "--full" in sys.argv
fails = []
def cli(*a):
    r = subprocess.run([sys.executable, str(ROOT / "bin/vpipe.py"), *a], capture_output=True, text=True, timeout=7200,
                       cwd=str(Path.home()), stdin=subprocess.DEVNULL)  # local cwd, not the network mount
    try:
        return r.returncode, json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:
        return r.returncode, {"raw": (r.stdout + r.stderr)[-2000:]}
rc, out = cli("check-fixture", "framac")
if out.get("proved") != exp["framac"]["proved"] or out.get("total") != exp["framac"]["total"]:
    fails.append(f"framac fixture: got {out}, expected {exp['framac']}")
rc, out = cli("check-fixture", "rust", *(["--full"] if full else []))
if out.get("extracted") != exp["rust"]["extracted"]:
    fails.append(f"rust extraction: got {out}, expected {exp['rust']['extracted']}")
if full and (out.get("proved") != exp["rust"]["proved"] or out.get("sorries") != 0):
    fails.append(f"lean proof: got {out}, expected {exp['rust']['proved']} proved, 0 sorries")
rc, out = cli("selftest")
if rc != 0:
    fails.append(f"vpipe selftest failed: {out}")
rc, _ = cli("--help")
print(json.dumps({"gate_ok": not fails, "failures": fails, "full": full}))
sys.exit(1 if fails else 0)
