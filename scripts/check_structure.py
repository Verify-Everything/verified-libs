#!/usr/bin/env python3
"""Check that every entry under libs/ follows the layout in STANDARDS.md.

Each libs/<library>/<version>/ must contain CLAIM.md (with complete front
matter and a non-empty "Not covered" section), spec/, proof/ and
pipeline/run.sh. Exits 1 and lists every problem if anything is missing.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBS = ROOT / "libs"
NAME = re.compile(r"^[a-z0-9][a-z0-9._-]*$")
REQUIRED_FIELDS = ["library", "version", "source", "tool", "tool_version", "strength", "status"]
STRENGTHS = {"functional", "contracts", "safety", "bounded"}
STATUSES = {"verified", "in-progress", "broken"}


def front_matter(text):
    m = re.match(r"^---\s*\n(.*?)\n---\s*\n", text, re.S)
    if not m:
        return None
    fields = {}
    for line in m.group(1).splitlines():
        line = line.split("#", 1)[0].strip()
        if ":" in line:
            key, value = line.split(":", 1)
            fields[key.strip()] = value.strip().strip("\"'")
    return fields


def section(text, heading):
    m = re.search(rf"^## {re.escape(heading)}\s*$(.*?)(?=^## |\Z)", text, re.S | re.M)
    if not m:
        return None
    body = re.sub(r"<!--.*?-->", "", m.group(1), flags=re.S)
    return body.strip()


def check_entry(entry):
    problems = []
    rel = entry.relative_to(ROOT).as_posix()
    for part in (entry.parent.name, entry.name):
        if not NAME.match(part):
            problems.append(f"{rel}: folder name '{part}' must use lowercase letters, digits, '.', '_' or '-'")
    for d in ("spec", "proof", "pipeline"):
        if not (entry / d).is_dir():
            problems.append(f"{rel}: missing {d}/")
    if not (entry / "pipeline" / "run.sh").is_file():
        problems.append(f"{rel}: missing pipeline/run.sh")
    claim = entry / "CLAIM.md"
    if not claim.is_file():
        problems.append(f"{rel}: missing CLAIM.md")
        return problems
    text = claim.read_text(encoding="utf-8")
    fm = front_matter(text)
    if fm is None:
        problems.append(f"{rel}/CLAIM.md: missing front matter (--- ... ---)")
        return problems
    for key in REQUIRED_FIELDS:
        if not fm.get(key):
            problems.append(f"{rel}/CLAIM.md: front matter field '{key}' is empty or missing")
    if fm.get("strength") and fm["strength"] not in STRENGTHS:
        problems.append(f"{rel}/CLAIM.md: strength must be one of {sorted(STRENGTHS)}")
    if fm.get("status") and fm["status"] not in STATUSES:
        problems.append(f"{rel}/CLAIM.md: status must be one of {sorted(STATUSES)}")
    if fm.get("version") and fm["version"] != entry.name:
        problems.append(f"{rel}/CLAIM.md: version '{fm['version']}' does not match folder '{entry.name}'")
    not_covered = section(text, "Not covered")
    if not not_covered or not_covered.lower().rstrip(".") in {"nothing", "none", "n/a"}:
        problems.append(f"{rel}/CLAIM.md: 'Not covered' must say what the proof does not cover")
    if fm.get("strength") == "bounded" and not section(text, "Bounds (only for `bounded`)"):
        problems.append(f"{rel}/CLAIM.md: bounded entries must list their bounds")
    return problems


def main():
    entries = sorted(v for lib in LIBS.iterdir() if lib.is_dir() for v in lib.iterdir() if v.is_dir()) if LIBS.is_dir() else []
    stray = sorted(p for p in LIBS.iterdir() if p.is_file() and p.name != "README.md") if LIBS.is_dir() else []
    problems = [f"libs/{p.name}: only library folders belong in libs/" for p in stray]
    for entry in entries:
        problems += check_entry(entry)
    if problems:
        print("Structure check failed:")
        for p in problems:
            print(f"  - {p}")
        return 1
    print(f"Structure check passed ({len(entries)} entr{'y' if len(entries) == 1 else 'ies'}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
