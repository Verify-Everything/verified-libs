#!/usr/bin/env python3
"""Check that the Rust bodies proved by Creusot are the real code.

Each function in a Creusot source file that is preceded by a marker comment

    // verbatim: <tree> <path> <signature line>

must, once proof annotations are removed, equal (line for line, ignoring common indentation)
the function with that exact signature line in <tree>/<path>, where <tree> is `upstream`
(the pinned upstream crate), `patched` (the same crate with rust/aeneas-friendly.patch) or
`both`. The signature must occur exactly once in that file.

Proof annotations removed: attribute lines `#[invariant(..)]` / `#[variant(..)]` (may span lines)
and ghost statements `snapshot!..;`, `let x = snapshot!(..);`, `x = snapshot!(..);`,
`proof_assert!..;` (one line each). Creusot checks that ghost code has no runtime effect.

Usage: check_verbatim.py --upstream DIR --patched DIR FILE...   (exit 1 on any mismatch)
"""
import argparse
import re
import sys
from pathlib import Path

MARK = re.compile(r"^\s*// verbatim: (upstream|patched|both) (\S+) (.+?)\s*$")
GHOST_HEAD = re.compile(r"^\s*(?:(?:let\s+(?:mut\s+)?)?\w+\s*=\s*)?(?:snapshot!|proof_assert!)\s*")


def is_ghost(line):
    """Exactly one `[let [mut] x =] snapshot!/proof_assert! <delimited>;` and nothing else."""
    m = GHOST_HEAD.match(line)
    if not m:
        return False
    rest = line[m.end():]
    if not rest or rest[0] not in "({":
        return False
    close = {"(": ")", "{": "}"}[rest[0]]
    depth = 0
    for k, ch in enumerate(rest):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
            if depth == 0:
                return ch == close and rest[k + 1:].strip() == ";"
    return False
ATTR_START = re.compile(r"^\s*#\[(?:invariant|variant)\(")


def fn_lines(lines, start):
    """Lines of the function whose signature is lines[start], up to its closing brace."""
    indent = len(lines[start]) - len(lines[start].lstrip())
    close = " " * indent + "}"
    for j in range(start, len(lines)):
        if lines[j].rstrip() == close:
            return lines[start:j + 1]
    raise ValueError(f"no closing brace for: {lines[start].strip()}")


def strip_annotations(body):
    """Drop proof-only lines. An attribute must end with `)]` and nothing after it."""
    out, i = [], 0
    while i < len(body):
        line = body[i]
        m = ATTR_START.match(line)
        if m:
            text, j, depth, end = line[m.end() - 1:], i, 0, None
            while end is None:
                for k, ch in enumerate(text):
                    if ch in "([{":
                        depth += 1
                    elif ch in ")]}":
                        depth -= 1
                        if depth == 0:
                            end = text[k + 1:]
                            break
                if end is None:
                    j += 1
                    if j >= len(body):
                        raise ValueError(f"unterminated attribute: {line.strip()}")
                    text = body[j]
            if end.strip() != "]":
                raise ValueError(f"code after a proof attribute: {body[j].strip()}")
            i = j + 1
            continue
        if not is_ghost(line):
            out.append(line)
        i += 1
    return out


def dedent(body):
    ind = min((len(l) - len(l.lstrip()) for l in body if l.strip()), default=0)
    return [l[ind:].rstrip() for l in body]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--upstream", required=True)
    ap.add_argument("--patched", required=True)
    ap.add_argument("files", nargs="+")
    a = ap.parse_args()
    trees = {"upstream": Path(a.upstream), "patched": Path(a.patched)}
    cache = {}

    def source(tree, path):
        if (tree, path) not in cache:
            cache[(tree, path)] = (trees[tree] / path).read_text().splitlines()
        return cache[(tree, path)]
    bad, n = 0, 0
    for f in a.files:
        lines = Path(f).read_text().splitlines()
        for i, line in enumerate(lines):
            m = MARK.match(line)
            if not m:
                continue
            which, path, sig = m.group(1), m.group(2), m.group(3)
            j = i + 1  # skip spec attributes between the marker and the signature
            while j < len(lines) and lines[j].strip() != sig:
                j += 1
            if j == len(lines):
                print(f"FAIL {f}: signature after marker not found: {sig}")
                bad += 1
                continue
            mine = dedent(strip_annotations(fn_lines(lines, j)))
            for tree in (["upstream", "patched"] if which == "both" else [which]):
                n += 1
                src = source(tree, path)
                hits = [k for k, l in enumerate(src) if l.strip() == sig]
                if len(hits) != 1:
                    print(f"FAIL {f}: '{sig}' occurs {len(hits)} times in {tree}/{path}")
                    bad += 1
                    continue
                theirs = dedent(fn_lines(src, hits[0]))
                if mine != theirs:
                    print(f"FAIL {f}: {tree} {path} {sig}")
                    import difflib
                    for d in difflib.unified_diff(theirs, mine, tree, f, lineterm="", n=1):
                        print("   ", d)
                    bad += 1
                else:
                    print(f"ok   {tree:8} {path} {sig}")
    print(f"{n - bad}/{n} functions match their source")
    return 1 if bad or n == 0 else 0


if __name__ == "__main__":
    sys.exit(main())
