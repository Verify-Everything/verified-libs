"""Admission standards for verified-libs, as machine checks.

Source: "verified-libs admission standards" (https://claude.ai/artifact/1tqQsrMgXckaNZQJVXPWvp),
approved by Yerin on 2026-10-24. An entry is `verified` only when all ten gates pass; there are no
partial admissions and no waivers. Everything else is a `candidate` (published under candidates/).

Pure functions: vpipe.py passes data in and writes what comes back.
"""
import datetime as dt
import hashlib
import json
import re
import subprocess
from pathlib import Path

LABELS = ["tested", "bounded", "no-ub", "safety-contracts", "full-correctness"]  # weakest first
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATUSES = ["verified", "candidate", "stale", "broken", "revoked"]

# Forbidden constructs (draft: "Trusted base and CI checks"). The axiom audit catches what these
# introduce at the kernel level; the text scan catches shortcuts the audit cannot see.
LEAN_FORBIDDEN = [
    (r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"^\s*(?:private\s+)?axiom\s", "axiom"),
    (r"\bnative_decide\b", "native_decide"), (r"\bbv_decide\b", "bv_decide"),
    (r"\bimplemented_by\b", "implemented_by"), (r"@\[\s*extern\b", "@[extern]"),
    (r"^\s*unsafe\s", "unsafe"), (r"^\s*(?:private\s+)?opaque\s", "opaque"),
    (r"set_option\s+debug\.skipKernelTC", "skipKernelTC"),
]
ACSL_FORBIDDEN = [(r"\badmit\b", "admit clause"), (r"\bcheck\s+(?:requires|ensures)\b", "check-only clause")]


def _strip_lean_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def forbidden_lean(proj: Path, files):
    hits = []
    for rel in sorted(set(files)):
        f = proj / rel
        if not f.exists():
            continue
        for i, line in enumerate(_strip_lean_comments(f.read_text(errors="replace")).splitlines(), 1):
            for pat, name in LEAN_FORBIDDEN:
                if re.search(pat, line):
                    hits.append({"file": rel, "line": i, "construct": name})
    return hits


def forbidden_framac(annotated: Path, files, wp_args):
    hits = []
    if "-wp-rte" not in wp_args:
        hits.append({"file": "vpipe.toml", "line": 0, "construct": "WP run without -wp-rte"})
    for rel in files:
        f = annotated / rel
        if not f.exists():
            continue
        text = f.read_text(errors="replace")
        for mm in re.finditer(r"/\*@.*?\*/|//@[^\n]*", text, re.S):
            line = text[:mm.start()].count("\n") + 1
            for pat, name in ACSL_FORBIDDEN:
                if re.search(pat, mm.group(0)):
                    hits.append({"file": rel, "line": line, "construct": name})
            if re.search(r"\bassumes?\b", mm.group(0)) and not re.search(r"\bbehavior\b|\bbehaviors\b", mm.group(0)):
                hits.append({"file": rel, "line": line, "construct": "assume outside a behavior"})
    return hits


def weakest(labels):
    known = [l for l in labels if l in LABELS]
    if len(known) < len(labels) or not labels:
        return "unlabelled"
    return min(known, key=LABELS.index)


def function_label(fn, tool, override):
    """The label a function earns. A declared label is a claim the reviewer checks; evidence caps it."""
    declared = override.get("label")
    if fn["status"] == "open":
        return "none"
    if override.get("verified_by") == "cbmc" and not (fn.get("cbmc") or {}).get("complete"):
        return "bounded"  # a complete harness (complete = true, no __CPROVER_assume) may keep its declared label
    if tool == "framac" and not fn.get("has_ensures", True):
        return "no-ub"
    if declared not in LABELS:
        return "unlabelled"
    return declared


def archive_sha256(src: Path, commit: str):
    """SHA-256 of `git archive` of the pinned commit (deterministic for a given git version)."""
    try:
        data = subprocess.run(["git", "archive", "--format=tar", commit], cwd=src, capture_output=True,
                              check=True, timeout=600).stdout
        return hashlib.sha256(data).hexdigest()
    except Exception as e:  # noqa: BLE001
        return f"unavailable ({e.__class__.__name__})"


def gates(m, res, overrides, history, mutants, container=None):
    """The ten admission gates. Each is {"pass": bool, "detail": str}. `history` is the list of
    earlier result dicts for this entry (newest first); `mutants` is the planted-bug run or None."""
    g = {}
    fi = res.get("functions") or {}
    fns = fi.get("functions", [])
    scope = m.get("scope", {})
    trust = m.get("trust", {})
    review = m.get("review", {})
    patches = m.get("patches", {})
    model = bool(res.get("model_crate"))
    container = container or {}
    equiv = set(patches.get("equivalence_theorems", []))
    proved = {t["name"] for t in (res.get("prove") or {}).get("theorems", []) if t.get("status") == "proved"}

    # 1 real code
    tool_patches = patches.get("files", [])
    fix_patches = {o.get("fix") for o in overrides.values() if o.get("fix")}
    unproved_tool_patches = [p for p in tool_patches if p not in fix_patches] if not (equiv and equiv <= proved) else []
    sha_pin, sha_now = m.get("archive_sha256"), res.get("archive_sha256")
    if not sha_pin or sha_pin != sha_now:
        g["real_code"] = {"pass": False, "detail": f"upstream archive SHA-256 not pinned in vpipe.toml (this run: {sha_now})"
                          if not sha_pin else f"upstream archive SHA-256 changed: pinned {sha_pin}, got {sha_now}"}
    elif model and not (trust.get("model_equivalence") and set(trust["model_equivalence"]) <= proved):
        g["real_code"] = {"pass": False, "detail": "proofs are about a model crate with no proved model-to-code equivalence"}
    elif [t for t in (res.get("prove") or {}).get("tool_patches", []) if not t.get("ok")]:
        g["real_code"] = {"pass": False, "detail": "tool patches without a passing equivalence harness: "
                          + str([t["id"] for t in res["prove"]["tool_patches"] if not t.get("ok")])}
    elif unproved_tool_patches:
        g["real_code"] = {"pass": False, "detail": f"tool-only patches without a proved equivalence: {unproved_tool_patches}"}
    else:
        g["real_code"] = {"pass": True, "detail": "pinned upstream source" + (" plus proved fixes" if fix_patches else "")}
    # 2 every function
    g["every_function"] = {"pass": bool(fi.get("complete")),
                           "detail": f"{fi.get('verified', 0) + fi.get('fixed', 0)}/{fi.get('total', 0)} functions verified or fixed"
                           + ("" if m.get("coverage", {}).get("targets") else "; targets/features covered not declared in [coverage]")}
    if g["every_function"]["pass"] and not m.get("coverage", {}).get("targets"):
        g["every_function"]["pass"] = False
    labels = [f.get("label", "none") for f in fns]
    # 3 all inputs
    bounded = [f["id"] for f in fns if f.get("label") == "bounded"]
    g["all_inputs"] = {"pass": not bounded and bool(fns), "detail": f"bounded-only functions: {bounded[:10]}" if bounded else "no bounded-only evidence"}
    # 4 full strength
    entry_label = weakest(labels) if fns else "none"
    g["full_strength"] = {"pass": entry_label == "full-correctness", "detail": f"entry strength {entry_label}"}
    # 5 spec first
    ok5 = bool(scope.get("properties")) and bool(scope.get("written")) and bool(scope.get("reviewed_by"))
    g["spec_first"] = {"pass": ok5, "detail": "success criteria written and reviewed" if ok5 else
                       "need [scope].properties, [scope].written (date) and [scope].reviewed_by"}
    # 6 not vacuous
    mm = mutants if mutants and mutants.get("commit") == m.get("commit") else None
    caught = mm and mm.get("total", 0) >= 10 and mm.get("caught") == mm.get("total") and not mm.get("invalid")
    chosen = mm and mm.get("chosen_by") and mm.get("chosen_by") != review.get("author")
    ok6 = bool(scope.get("test_vectors")) and bool(caught) and bool(chosen)
    g["not_vacuous"] = {"pass": ok6, "detail": (f"planted bugs {mm.get('caught')}/{mm.get('total')} caught ({mm.get('invalid', 0)} invalid), chosen by {mm.get('chosen_by') or 'NOBODY'}"
                                                if mm else "no planted-bug run on this commit (`vpipe mutate`)")
                        + ("" if scope.get("test_vectors") else "; [scope].test_vectors missing")}
    # 7 clean trusted base
    listed = set(trust.get("models", [])) | set(trust.get("axioms", []))
    extra_axioms = sorted({a for t in (res.get("prove") or {}).get("theorems", []) for a in t.get("axioms", []) if a not in listed})
    assumed = set((res.get("extract") or {}).get("assumed_axioms", []))
    unlisted_models = sorted(assumed - listed)
    forb = res.get("forbidden", [])
    replay = (res.get("prove") or {}).get("replay")
    replay_ok = m.get("tool") != "lean-aeneas" or bool(replay and replay.get("ok"))
    ok7 = not forb and not extra_axioms and not unlisted_models and replay_ok
    g["trusted_base"] = {"pass": ok7, "detail": "clean; kernel replay passed" if ok7 and m.get("tool") == "lean-aeneas" else "clean" if ok7 else
                         f"forbidden: {len(forb)}; axioms not listed in [trust]: {extra_axioms[:10]}; std models not listed: {unlisted_models[:10]}"
                         + ("" if replay_ok else "; leanchecker replay " + ("failed" if replay else "not run"))}
    # 8 independent cross-check
    cc = res.get("crosscheck") or []
    g["cross_check"] = {"pass": bool(cc) and all(t["ok"] for t in cc),
                        "detail": f"{len(cc)} differential cross-check command(s)" if cc else "no [crosscheck] commands"}
    # 9 reproducible from scratch
    def outcome(h):
        return sorted((t["name"], t.get("status")) for t in (h.get("prove") or {}).get("theorems", [])), \
            (h.get("prove") or {}).get("proved"), (h.get("prove") or {}).get("total")
    clean_runs = [h for h in [res] + history if h.get("clean") and h.get("commit") == m.get("commit")
                  and h.get("toolchain_digest") == res.get("toolchain_digest")][:2]
    same = len(clean_runs) == 2 and outcome(clean_runs[0]) == outcome(clean_runs[1]) and (res.get("prove") or {}).get("ok")
    pinned = container.get("digest")
    in_container = bool(pinned) and all(h.get("container_digest") == pinned for h in clean_runs)
    g["reproducible"] = {"pass": bool(same and in_container),
                         "detail": f"{len(clean_runs)} matching clean run(s) on this toolchain"
                         + ("" if pinned else "; no container digest pinned in toolchain/versions.toml [container]")
                         + ("" if not pinned or in_container else "; runs not inside the pinned container")}
    # 10 two reviews
    ok10 = bool(review.get("maintainer")) and bool(review.get("adversarial")) and review.get("maintainer") != review.get("author")
    g["two_reviews"] = {"pass": ok10, "detail": "maintainer and adversarial sign-offs recorded" if ok10 else "need [review].maintainer and [review].adversarial"}
    return g, entry_label


def entry_status(m, res, g, admitted, history, soundness_hits, max_age_days=14):
    """Lifecycle (standard, "Lifecycle after admission"). `admitted` = the entry lives under libs/.
    A newer upstream release does not change this entry: the new version is a separate, stale entry."""
    if m.get("status", {}).get("revoked"):
        return "revoked"
    if res.get("commit") != m.get("commit"):
        return "stale"          # manifest moved to a new commit that has not been re-proved
    p = res.get("prove") or {}
    green = p.get("ok") and all(x["pass"] for x in g.values()) and not soundness_hits
    if admitted:
        if not green:
            return "broken"
        runs = [h for h in [res] + history if (h.get("prove") or {}).get("ok") and h.get("clean")]
        last = max((h.get("finished", "") for h in runs), default="")
        try:
            age = (dt.datetime.now(dt.timezone.utc) - dt.datetime.strptime(last, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)).days
        except ValueError:
            return "broken"
        return "broken" if age > max_age_days else "verified"
    # Candidates are never "verified": admission is the move to libs/ (`vpipe admit`) once all gates pass.
    return "candidate"


def claim_card(m, res, g, entry_label, status, archive_sha, upstream):
    fi = res.get("functions") or {}
    fns = fi.get("functions", [])
    p = res.get("prove") or {}
    tc = res.get("toolchain", {})
    full = sum(f.get("label") == "full-correctness" for f in fns)
    open_ = [f for f in fns if f["status"] == "open"]
    trust = m.get("trust", {})
    scope = m.get("scope", {})
    review = m.get("review", {})
    axioms = sorted({a for t in p.get("theorems", []) for a in t.get("axioms", [])})
    tool_names = {"lean-aeneas": "Lean 4 + Aeneas", "framac": "Frama-C WP"}
    tool_version = ", ".join(f"{k} {v}" for k, v in tc.items() if k not in ("aeneas_dir", "why3_provers"))
    front = {"library": m["name"], "version": m.get("version", ""), "source": m["upstream"], "commit": m["commit"],
             "archive_sha256": archive_sha or "", "tool": tool_names.get(m["tool"], m["tool"]),
             "tool_version": (tool_version + "; " if tool_version else "") + (res.get("container_digest") or res.get("toolchain_digest") or ""),
             "strength": entry_label if entry_label in LABELS else
             f"tested  # lowest label; real value: {entry_label} (functions without a label in functions.toml, or open)",
             "status": status, "functions": f"{full}/{fi.get('total', 0)}"}
    lines = ["---"] + [f"{k}: {v}" for k, v in front.items()] + ["---", "",
        f"# {m['name']} {m.get('version', '')}: CLAIM", "",
        "<!-- Generated by `vpipe card` from the latest run. People edit vpipe.toml ([scope], [trust], [review])"
        " and functions.toml, never this file. -->", "",
        f"Status: {status}",
        f"Entry strength: {entry_label}",
        f"Functions: {full}/{fi.get('total', 0)} at full-correctness ({fi.get('verified', 0) + fi.get('fixed', 0)} verified or fixed)",
        "", "## Success criteria (written before proof work)",
        f"- Written: {scope.get('written', 'NOT RECORDED')}. Reviewed by: {scope.get('reviewed_by', 'NOBODY YET')}",
        "- Every function in the pinned source (all features, all supported targets, trait impls) reaches"
        " full-correctness for all inputs.",
        "- Library-specific properties:"] + [f"  - {x}" for x in scope.get("properties", [])] + [
        "", "## Code",
        f"- Upstream: {m['upstream']} @ {m['commit']}, archive SHA-256 {archive_sha}",
        f"- Fork (if any): {m.get('fork', 'none')}",
        f"- Features and targets covered: {', '.join(m.get('coverage', {}).get('targets', [])) or 'NOT DECLARED'}"
        + (f"; variants: {', '.join(v['name'] for v in m.get('variant', []))}" if m.get("variant") else ""),
        (f"- Newer upstream release {upstream.get('latest')} exists; it is NOT verified (stale) until re-proved" if upstream and upstream.get("newer")
         else f"- Upstream releases checked {upstream.get('checked')}: pinned version is the latest" if upstream else "- Upstream releases: not checked yet (`vpipe check-upstream`)"),
        "", "## Specification",
        f"- Plain words: {scope.get('summary', 'NOT WRITTEN')}",
        f"- Formal spec files: {', '.join(scope.get('spec_files', [])) or 'not listed'}",
        f"- Matches standard / test vectors: {', '.join(scope.get('test_vectors', [])) or 'NONE'}",
        "", "## Proof",
        f"- Tool(s) and versions: {m['tool']}; " + ", ".join(f"{k} {v}" for k, v in tc.items() if k not in ('aeneas_dir', 'why3_provers'))
        + f"; toolchain digest {res.get('toolchain_digest', 'unknown')}; container digest {res.get('container_digest') or 'NOT IN A PINNED CONTAINER'}",
        f"- Kernel replay (leanchecker): {((p.get('replay') or {}).get('ok') and 'passed') or ('FAILED' if p.get('replay') else 'not run')}" if m['tool'] == 'lean-aeneas' else "- Kernel replay: not applicable",
        f"- Theorems / goals: {p.get('proved', 0)}/{p.get('total', 0)} proved, {p.get('sorries', 0)} sorries, {p.get('axiom_thms', 0)} with extra axioms",
        "- Per-function results: below, and functions.toml for declared labels and evidence",
        f"- Planted-bug check: {g['not_vacuous']['detail']}",
        f"- Differential cross-check of the translation: {g['cross_check']['detail']}",
        "", "## Trusted base",
        f"- Axioms reported by the checker: {', '.join(sorted(STD_AXIOMS))}" + (f", plus {', '.join(axioms)}" if axioms else ""),
        f"- Std or library models: {', '.join(trust.get('models', [])) or 'none listed'}"
        + (f" (unlisted models assumed by the extraction: {len(set((res.get('extract') or {}).get('assumed_axioms', [])) - set(trust.get('models', [])))})"
           if (res.get("extract") or {}).get("assumed_axioms") else ""),
        f"- Tool assumptions: {trust.get('tool_assumptions', 'translator (Aeneas/Charon) faithful; Lean kernel sound' if m['tool'] == 'lean-aeneas' else 'Frama-C WP memory model and provers sound')}",
        f"- Unsafe / FFI boundaries: {trust.get('unsafe', 'not listed')}",
        f"- Patches applied: {', '.join(m.get('patches', {}).get('files', [])) or 'none'}" + ("; MODEL CRATE" if res.get("model_crate") else ""),
        f"- Forbidden constructs found: {len(res.get('forbidden', []))}",
        "", "## Not covered",
    ]
    lines += [f"- `{f['id']}`: {f.get('why', 'open')}" for f in open_] or ["(nothing)"]
    bounded = [f for f in fns if f.get("label") == "bounded"]
    if bounded:
        lines += ["", "## Bounds (only for `bounded`)"] + [f"- `{f['id']}`: {f.get('bounds', 'bounds not recorded')}" for f in bounded]
    lines += ["", "## How to re-check", "", "```bash", "./pipeline/run.sh", "```"]
    lines += ["", "## Bugs found and fixes"]
    fixes = [f for f in fns if f["status"] == "fixed"]
    lines += [f"- `{f['id']}`: {f.get('note', '')}" for f in fixes] or ["- none recorded"]
    lines += ["", "## Admission gates", "", "| Gate | Pass | Detail |", "|---|---|---|"]
    lines += [f"| {k.replace('_', ' ')} | {'yes' if v['pass'] else 'NO'} | {v['detail']} |" for k, v in g.items()]
    lines += ["", "## Per-function results", "", "| Function | Status | Label | Evidence |", "|---|---|---|---|"]
    for f in fns:
        ev = ", ".join(f.get("theorems", [])[:4]) or (f"{f['goals']['proved']}/{f['goals']['total']} WP goals" if f.get("goals") else "")
        lines.append(f"| `{f['id']}` | {f['status']} | {f.get('label', '')} | {ev} |")
    lines += ["", "## Credits"] + [f"- {c}" for c in m.get("credits", [])] if m.get("credits") else ["", "## Credits", "- not recorded"]
    lines += ["", "## Review",
              f"- Maintainer sign-off: {review.get('maintainer', 'NOT YET')}",
              f"- Adversarial review: {review.get('adversarial', 'NOT YET')}",
              f"- Last clean CI re-check: {res.get('finished') if res.get('clean') else 'no clean run yet'}"
              + (f" ({res['ci_run']})" if res.get("ci_run") else ""), ""]
    return "\n".join(lines)
