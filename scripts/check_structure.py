#!/usr/bin/env python3
"""Check that every entry under libs/ and candidates/ follows STANDARDS.md.

Each <area>/<library>/<version>/ must contain CLAIM.md (complete front matter),
spec/, proof/ and pipeline/run.sh. libs/ holds admitted entries only: strength
full-correctness, all functions, both review sign-offs, and for status verified
an empty "Not covered". Everything weaker belongs in candidates/.
Exits 1 and lists every problem.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBS = ROOT / "libs"
CANDIDATES = ROOT / "candidates"
NAME = re.compile(r"^[a-z0-9][a-z0-9._-]*$")
REQUIRED_FIELDS = ["library", "version", "source", "commit", "archive_sha256", "tool", "tool_version",
                   "strength", "status", "functions"]
STRENGTHS = {"full-correctness", "safety-contracts", "no-ub", "bounded", "tested"}
STATUSES = {"candidate", "verified", "stale", "broken", "revoked"}
ADMITTED = {"verified", "stale", "broken", "revoked"}   # statuses allowed under libs/


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
    if fm.get("commit") and not re.fullmatch(r"[0-9a-f]{40}", fm["commit"]):
        problems.append(f"{rel}/CLAIM.md: commit must be a full 40-hex hash")
    fn = re.fullmatch(r"(\d+)/(\d+)", fm.get("functions", ""))
    if fm.get("functions") and not fn:
        problems.append(f"{rel}/CLAIM.md: functions must look like N/M")
    admitted_area = entry.parent.parent == LIBS
    if admitted_area:
        if fm.get("status") not in ADMITTED:
            problems.append(f"{rel}/CLAIM.md: libs/ holds admitted entries only; status '{fm.get('status')}' belongs in candidates/")
        if fm.get("strength") != "full-correctness":
            problems.append(f"{rel}/CLAIM.md: only full-correctness is admitted; move to candidates/")
        if fn and fn.group(1) != fn.group(2):
            problems.append(f"{rel}/CLAIM.md: every function must be verified to be admitted ({fm['functions']})")
        review = section(text, "Review") or ""
        for line in ("Maintainer sign-off", "Adversarial review"):
            if not re.search(rf"{line}:\s*[^<\s]", review):
                problems.append(f"{rel}/CLAIM.md: '{line}' is missing")
        if fm.get("status") == "verified":
            not_covered = section(text, "Not covered") or ""
            if re.search(r"^\s*-\s*\S", not_covered, re.M):
                problems.append(f"{rel}/CLAIM.md: 'Not covered' must be empty for status verified")
            if re.search(r"<[a-z][^>]*>", text):
                problems.append(f"{rel}/CLAIM.md: template placeholders remain")
    elif fm.get("status") in ("verified",):
        problems.append(f"{rel}/CLAIM.md: candidates are never 'verified'")
    if fm.get("strength") == "bounded" and not section(text, "Bounds (only for `bounded`)"):
        problems.append(f"{rel}/CLAIM.md: bounded entries must list their bounds")
    return problems


def main():
    entries, problems = [], []
    for area in (LIBS, CANDIDATES):
        if not area.is_dir():
            continue
        entries += sorted(v for lib in area.iterdir() if lib.is_dir() for v in lib.iterdir() if v.is_dir())
        problems += [f"{area.name}/{p.name}: only library folders belong here"
                     for p in sorted(area.iterdir()) if p.is_file() and p.name != "README.md"]
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
