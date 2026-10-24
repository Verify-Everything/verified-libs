#!/usr/bin/env python3
"""vpipe: on-demand formal verification pipeline.

Commands
  setup [lean|framac|all]       install pinned toolchains (idempotent, restores mathlib cache)
  new <lib> --lang rust|c ...   scaffold a library manifest and proof folder
  run <lib> [--agent] [--clean] fetch -> extract -> prove -> admission gates -> CLAIM.md
  card <lib>                    re-evaluate the ten admission gates, rewrite CLAIM.md
  mutate <lib> [--suggest N]    planted-bug check from the reviewer's mutants.toml (gate 6)
  check-upstream [lib]          record newer upstream releases (stale marking) [--scaffold]
  admit <lib>                   candidates/<name>/<version> -> libs/ when every gate passes
  next <lib> / take <lib> FN --by NAME
                                work queue for many sessions on one library
  export <lib> [--dest REPO]    copy an entry into a verified-libs clone (candidates/ or libs/)
  run-all [--agent]             run every library manifest
  report                        rebuild results/SUMMARY.md from every library's latest result
  selftest [--full]             prove the fixtures end to end; gate for any self-change
  improve [--goal TEXT] [--propose]
                                self-update: read notes + results, change own code, selftest,
                                keep or roll back, log why in self/CHANGELOG.md
  upgrade-tools                 try newer Aeneas release; keep only if selftest passes
  rollback [SNAPSHOT]           restore the pipeline code from a snapshot
"""
import argparse, datetime as dt, hashlib, json, os, re, shutil, subprocess, sys, tarfile, tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import standards  # noqa: E402  (admission gates, labels, claim cards)

ROOT = Path(__file__).resolve().parent.parent           # the pipeline folder
# Shared lessons folder: the project's notes when present, else notes/ inside the pipeline.
_PROJECT_NOTES = Path("/mnt/project-files/verification-notes")
NOTES = Path(os.environ.get("VPIPE_NOTES") or (_PROJECT_NOTES if _PROJECT_NOTES.exists() else ROOT / "notes"))
VH = Path(os.environ.get("VPIPE_HOME", Path.home() / ".vpipe"))   # local toolchains
WORK = Path(os.environ.get("VPIPE_WORK", Path.home() / "vpipe-work"))  # local checkouts/builds
# Paths the self-update loop may change. Proofs, results, snapshots and notes are never touched.
# The gate (self/gate.py) and its fixtures (selftest/) are protected so a self-change cannot
# relax the test that judges it.
SELF_EDITABLE = ["bin", "toolchain", "templates", "checklists", "self/BACKLOG.md",
                 "self/CHANGELOG.md", "README.md", "VERSION", "bootstrap.sh"]
SELF_FORBIDDEN = ["proofs", "results", "self/snapshots", "libraries", "libs", "candidates", "selftest",
                  "self/gate.py", "toolchain/soundness.toml"]


def now():
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def log(*a):
    print("[vpipe]", *a, file=sys.stderr, flush=True)


def sh(cmd, cwd=None, env=None, check=True, capture=False, timeout=None):
    e = dict(os.environ)
    e["PATH"] = f"{VH}/bin:{VH}/aeneas:{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + e.get("PATH", "")
    if env:
        e.update(env)
    if cwd is None:
        # Never inherit the caller's cwd: on the network mount getcwd() sometimes fails, which
        # made setup scripts die with "cannot get cwd" inside the gate.
        WORK.mkdir(parents=True, exist_ok=True)
        cwd = WORK
    log("$", cmd if isinstance(cmd, str) else " ".join(map(str, cmd)))
    r = subprocess.run(cmd, cwd=cwd, env=e, shell=isinstance(cmd, str), text=True, timeout=timeout,
                       stdin=subprocess.DEVNULL,
                       capture_output=capture)
    if check and r.returncode != 0:
        if capture:
            sys.stderr.write((r.stdout or "")[-4000:] + (r.stderr or "")[-4000:])
        tail = ((r.stderr or "") if capture else "")[-600:]
        raise SystemExit(f"command failed ({r.returncode}): {cmd}" + (f"\n{tail}" if tail else ""))
    return r


def versions():
    return tomllib.loads((ROOT / "toolchain/versions.toml").read_text())


# Entry layout (admission standard): one folder per library version.
#   libs/<name>/<version>/        admitted entries (status verified, or broken/revoked after admission)
#   candidates/<name>/<version>/  everything else, published as "not verified"
#   libraries/<lib>/              older layout, still read (a symlink there is ignored)
# An entry id is "<name>/<version>"; a bare "<name>" works while only one version exists.
ENTRY_ROOTS = ("libs", "candidates")


def locate(lib):
    parts = lib.strip("/").split("/")
    if len(parts) == 2:
        for r in ENTRY_ROOTS:
            d = ROOT / r / parts[0] / parts[1]
            if (d / "vpipe.toml").exists():
                return d
        return None
    found = [d for r in ENTRY_ROOTS for d in sorted((ROOT / r / lib).glob("*")) if (d / "vpipe.toml").exists()]
    if len(found) > 1:
        raise SystemExit(f"{lib} has several versions ({', '.join(str(d.relative_to(ROOT)) for d in found)}); "
                         f"name one as {lib}/<version>")
    if found:
        return found[0]
    d = ROOT / "libraries" / lib
    return d if (d / "vpipe.toml").exists() else None


def entry_key(lib):
    """Results key: "<name>/<version>" for libs/ and candidates/ entries, else the old name."""
    d = locate(lib)
    for r in ENTRY_ROOTS:
        if d and d.parent.parent == ROOT / r:
            return f"{d.parent.name}/{d.name}"
    return lib


def admitted(lib):
    d = locate(lib)
    return bool(d) and d.parent.parent == ROOT / "libs"


def results_dir(lib):
    return ROOT / "results" / entry_key(lib)


def manifest_path(lib):
    d = locate(lib)
    return d / "vpipe.toml" if d else ROOT / "libraries" / f"{lib}.toml"


def proof_dir(lib, m):
    """Where the proof project lives. In the verified-libs layout that is <entry>/proof/ (beside
    CLAIM.md, spec/ and pipeline/run.sh); older folders hold the project at the top."""
    d = locate(lib)
    if d:
        return d / "proof" if (d / "proof").is_dir() else d
    return ROOT / m.get("proofs_dir", f"proofs/{lib}")


def entry_dir(lib, m):
    return locate(lib) or proof_dir(lib, m)


def all_libraries():
    ids = {f"{p.parent.parent.name}/{p.parent.name}" for r in ENTRY_ROOTS for p in (ROOT / r).glob("*/*/vpipe.toml")}
    lib_dir = ROOT / "libraries"
    ids |= {p.parent.name for p in lib_dir.glob("*/vpipe.toml") if not p.parent.is_symlink()}
    ids |= {p.stem for p in lib_dir.glob("*.toml")}
    return sorted(ids)


def manifest(lib):
    p = manifest_path(lib)
    if not p.exists():
        raise SystemExit(f"no manifest {p}; create one with `vpipe new {lib}`")
    m = tomllib.loads(p.read_text())
    for k in ("name", "lang", "tool", "upstream", "commit"):
        if k not in m:
            raise SystemExit(f"{p}: missing required key {k!r}")
    return m


# ---------------------------------------------------------------- setup
def setup(which="all", tries=3):
    """Network installs flake now and then (seen once in the gate); retry before failing."""
    for i in range(tries):
        try:
            return _setup(which)
        except SystemExit:
            if i == tries - 1:
                raise
            log(f"setup failed, retrying ({i + 2}/{tries})")


def _setup(which):
    v = versions()
    info = {}
    if which in ("lean", "all"):
        r = sh(["bash", ROOT / "toolchain/setup-lean.sh", v["aeneas"]["tag"], v["aeneas"]["url"],
                v["lean"]["version"], v["lean"]["url"], v["lean"]["elan_init"],
                ",".join(v["rust"]["components"])], capture=True)
        info.update(json.loads(r.stdout.strip().splitlines()[-1]))
    if which in ("framac", "all"):
        r = sh(["bash", ROOT / "toolchain/setup-framac.sh", " ".join(v["framac"]["nix_packages"])],
               capture=True)
        info.update(json.loads(r.stdout.strip().splitlines()[-1]))
    (VH / "installed.json").write_text(json.dumps(info, indent=2))
    return info


def mathlib_cache_key():
    """Key = Aeneas commit + Lean version: both fix the mathlib revision."""
    v = versions()
    return f"aeneas-{v['aeneas']['commit'][:7]}-lean-{v['lean']['version']}"


def cache_dirs():
    env = os.environ.get("VPIPE_CACHE_DIRS")
    dirs = env.split(":") if env else versions()["mathlib"]["cache_dirs"]
    return [Path(d) if Path(d).is_absolute() else ROOT / d for d in dirs]


def restore_lake_packages(proj: Path):
    """Give the project a built .lake/packages (mathlib etc.) without compiling it for hours.
    One shared copy per cache key lives in $VPIPE_HOME/lake/<key>/ and is symlinked into every
    project, so N libraries cost one mathlib on disk (3-8 GB each otherwise; toolkit thread hit
    "No space left"). Tarball layout: .lake/packages/... plus lake-manifest.json."""
    key = mathlib_cache_key()
    shared = VH / "lake" / key
    if damaged_oleans(shared / ".lake/packages"):
        # A full disk during unpacking leaves zero-byte .olean files that lake then trusts
        # (percent-encoding thread). Unpack again from the tarball.
        log(f"zero-byte .olean files in {shared}; unpacking it again")
        shutil.rmtree(shared, ignore_errors=True)
    own = proj / ".lake/packages"
    if not own.is_symlink() and (own / "mathlib/.lake/build").exists():
        bad = damaged_oleans(own)
        if not bad:
            return True
        raise SystemExit(f"{own} has {len(bad)} zero-byte .olean files (full disk?); delete {own} and run again")
    if not (shared / ".lake/packages/mathlib/.lake/build").exists():
        short = versions()["aeneas"]["commit"][:7]
        for d in cache_dirs():
            if not d.exists():
                continue
            cands = sorted(d.glob(f"*{key}*.tar*")) or sorted(d.glob(f"*{short}*mathlib*.tar*"))
            for c in (c for c in cands if not c.name.endswith(".part")):
                log(f"unpacking lake packages from {c} into {shared}")
                shutil.rmtree(shared, ignore_errors=True)
                shared.mkdir(parents=True)
                sh(f"tar -xf '{c}' -C '{shared}'", check=False)
                if (shared / ".lake/packages/mathlib").exists():
                    break
            if (shared / ".lake/packages/mathlib").exists():
                break
    if not (shared / ".lake/packages/mathlib").exists():
        log("no mathlib cache found; trying `lake exe cache get`, else lake compiles mathlib (slow)")
        return False
    (proj / ".lake").mkdir(parents=True, exist_ok=True)
    link = proj / ".lake/packages"
    if link.is_symlink() or not link.exists():
        if link.is_symlink():
            link.unlink()
        link.symlink_to(shared / ".lake/packages", target_is_directory=True)
    if not (proj / "lake-manifest.json").exists() and (shared / "lake-manifest.json").exists():
        shutil.copy(shared / "lake-manifest.json", proj / "lake-manifest.json")
    return True


def damaged_oleans(pk: Path, limit=20):
    bad = []
    if pk.exists():
        for dirpath, _, files in os.walk(pk, followlinks=False):
            for f in files:
                if f.endswith(".olean") and os.path.getsize(os.path.join(dirpath, f)) == 0:
                    bad.append(os.path.join(dirpath, f))
                    if len(bad) >= limit:
                        return bad
    return bad


def share_lake_packages(proj: Path):
    """After `lake exe cache get` or a source build, move the project's own .lake/packages into the
    shared $VPIPE_HOME/lake/<key>/ and symlink it back (toolkit thread: otherwise every project
    re-downloads mathlib and disk grows by gigabytes per library)."""
    own = proj / ".lake/packages"
    shared = VH / "lake" / mathlib_cache_key()
    if own.is_symlink() or not (own / "mathlib/.lake/build").exists():
        return
    if (shared / ".lake/packages/mathlib/.lake/build").exists():
        return  # someone already shared one; keep this project's copy as is
    (shared / ".lake").mkdir(parents=True, exist_ok=True)
    shutil.move(str(own), str(shared / ".lake/packages"))
    if (proj / "lake-manifest.json").exists():
        shutil.copy(proj / "lake-manifest.json", shared / "lake-manifest.json")
    own.symlink_to(shared / ".lake/packages", target_is_directory=True)
    log(f"shared lake packages at {shared}")


def save_lake_packages(proj: Path):
    """After a from-source mathlib build, publish it so no other session repeats it."""
    cache = ROOT / "cache"  # never write into another thread's folder
    cache.mkdir(parents=True, exist_ok=True)
    out = cache / f"lake-packages-{mathlib_cache_key()}.tar.zst"
    if out.exists() or not (proj / ".lake/packages/mathlib/.lake/build").exists():
        return
    tmp = Path(str(out) + ".part")
    sh(f"tar -C '{proj}' -cf - .lake/packages lake-manifest.json | zstd -T0 -3 > '{tmp}' && mv '{tmp}' '{out}'")
    log(f"saved mathlib cache to {out}")


def mirror(src: Path, dst: Path, delete=False, skip=(".lake", ".git")):
    """Copy src over dst, skipping build dirs. With delete, remove files in dst missing from src."""
    dst.mkdir(parents=True, exist_ok=True)
    if delete:
        for f in sorted(dst.rglob("*"), reverse=True):
            rel = f.relative_to(dst)
            if rel.parts[0] in skip:
                continue
            if not (src / rel).exists():
                shutil.rmtree(f) if f.is_dir() else f.unlink()
    shutil.copytree(src, dst, dirs_exist_ok=True, ignore=shutil.ignore_patterns(*skip))


# ---------------------------------------------------------------- fetch
def fetch(m):
    src = WORK / m["name"] / "src"
    if not (src / ".git").exists():
        src.parent.mkdir(parents=True, exist_ok=True)
        sh(["git", "clone", "-q", m["upstream"], src])
    sh(["git", "fetch", "-q", "origin", m["commit"]], cwd=src, check=False)
    sh(["git", "checkout", "-q", "--detach", m["commit"]], cwd=src)
    return src


# ---------------------------------------------------------------- lean / aeneas
def extract_rust(m, src, proj):
    x = m.get("extract", {})
    crate = src / x.get("crate_dir", ".")
    llbc = WORK / m["name"] / f"{m['name']}.llbc"
    cmd = ["charon", "cargo", *x.get("charon_args", ["--preset=aeneas"]), "--dest-file", str(llbc)]
    if x.get("sysroot_default"):
        cmd += ["--sysroot", "default"]
    cargo_args = list(x.get("cargo_args", []))
    # Pin dependencies: a reviewed Cargo.lock in proofs/<lib>/ is copied in and cargo runs --locked,
    # so Charon never silently sees newer dependency versions (crc32fast thread).
    lock = proj / x.get("cargo_lock", "Cargo.lock")
    if lock.exists():
        shutil.copy(lock, crate / "Cargo.lock")
        cargo_args.append("--locked")
    if cargo_args:
        cmd += ["--", *cargo_args]
    r = sh(cmd, cwd=crate, check=False, capture=True)
    if r.returncode != 0:
        return {"ok": False, "stage": "charon", "log": (r.stdout + r.stderr)[-6000:]}
    mod = module_name(m)
    sub = extracted_rel(m)
    if sub.endswith("Extracted"):  # only wipe folders that hold nothing but generated code
        shutil.rmtree(proj / sub, ignore_errors=True)
    render_lakefile(proj)
    # Output lands in <proj>/<Module>/Extracted/{Types,Funs}.lean, imported as <Module>.Extracted.*
    r = sh(["aeneas", "-backend", "lean", str(llbc), "-dest", str(proj), "-subdir", sub,
            "-split-files", *x.get("aeneas_args", [])], check=False, capture=True)
    text = ANSI_RE.sub("", r.stdout + r.stderr)
    # Aeneas exits non-zero when it skips unsupported items but still writes the rest. Treat the run
    # as usable if Funs.lean exists and list what was skipped: that list decides the scope.
    unsupported = [{"error": e.strip(), "source": src_.strip()} for e, src_ in
                   re.findall(r"\[Error\]\s*([^\n]+)\n(?:Source: ([^\n]+))?", text)]
    ext = proj / sub
    assumed = install_externals(proj / externals_rel(m), ext)
    # Logged, semantics-preserving fix-ups for gaps in the Aeneas Lean library (percent-encoding).
    post = []
    for script in x.get("postprocess", []):
        pr = sh([sys.executable, "-I", str(proj / script), str(ext)], cwd=proj, check=False, capture=True)
        post.append({"script": script, "ok": pr.returncode == 0, "out": (pr.stdout + pr.stderr)[-1500:]})
    # Optional strictness: errors not matching allowed_errors, or changed std-model templates, fail the run.
    unexpected = [u for u in unsupported if "allowed_errors" in x and
                  not any(re.search(a, u["error"]) for a in x["allowed_errors"])]
    strict = x.get("strict_externals", False) and bool(template_changes)
    ok = (ext / "Funs.lean").exists() and not unexpected and not strict and all(q["ok"] for q in post)
    return {"ok": ok, "stage": "aeneas", "aeneas_rc": r.returncode, "postprocess": post,
            "unexpected_errors": unexpected[:50],
            "unsupported": unsupported[:100], "assumed_axioms": assumed,
            "external_template_changes": list(template_changes),
            "warnings": [w.strip() for w in re.findall(r"\[Warn\s*\]\s*([^\n]+)", text)][:50],
            "log": re.sub(r"[^\n]*(Translated|Post-processed|Applied prepasses)[^\n]*\n?", "", text)[-6000:]}


ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]")


template_changes = []  # filled by install_externals, reported in the extract result


def install_externals(keep, ext):
    """Aeneas writes *External_Template.lean with one `axiom` per std function it has no model for.
    Hand-written versions live in <Module>/External/ (kept across runs) and are copied in; the first
    time, the template is used as-is and saved there to refine. Returns the axioms still assumed."""
    assumed = []
    template_changes.clear()
    for t in sorted(ext.glob("*External_Template.lean")):
        name = t.name.replace("_Template", "")
        mine = keep / name
        seen = keep / (t.name + ".seen")   # the template as it was when External/ was last written
        if not mine.exists():
            keep.mkdir(parents=True, exist_ok=True)
            shutil.copy(t, mine)
            shutil.copy(t, seen)
        elif seen.exists() and seen.read_text() != t.read_text():
            # Aeneas now wants different std models (new, renamed or removed). Say so up front
            # instead of leaving it to surface as a Lean build error.
            old_ax = set(re.findall(r"^axiom\s+(\S+)", seen.read_text(), re.M))
            new_ax = set(re.findall(r"^axiom\s+(\S+)", t.read_text(), re.M))
            template_changes.append({"file": name, "added": sorted(new_ax - old_ax),
                                     "removed": sorted(old_ax - new_ax)})
            shutil.copy(t, keep / (t.name + ".new"))
        elif not seen.exists():
            shutil.copy(t, seen)
        # Exact check (percent-encoding's check_externals.py): the hand-written file must model the
        # same set of Rust functions the fresh template asks for.
        fun = re.compile(r'@\[[^\]]*rust_fun\s+"([^"]+)"', re.S)
        want, have = set(fun.findall(t.read_text())), set(fun.findall(mine.read_text()))
        if want != have:
            template_changes.append({"file": name, "needed_not_modelled": sorted(want - have),
                                     "modelled_not_needed": sorted(have - want)})
        shutil.copy(mine, ext / name)
        t.unlink()  # the template would clash with the real file under `lake build`
        assumed += re.findall(r"^axiom\s+(\S+)", mine.read_text(), re.M)
    return assumed


def extracted_rel(m):
    """Where Aeneas output goes inside the proof project (generated, replaced every run)."""
    return m.get("extract", {}).get("subdir") or f"{module_name(m)}/Extracted"


def externals_rel(m):
    """Hand-written std models, kept across runs and copied into the extracted folder."""
    return m.get("extract", {}).get("externals_dir") or f"{module_name(m)}/External"


def theorem_dirs(m):
    return m.get("proofs", {}).get("dirs") or [module_name(m)]


def module_name(m):
    return m.get("extract", {}).get("module") or "".join(w.title() for w in re.split(r"[-_]", m["name"]))


def sync_back(local, proj, m):
    """Local build copy -> shared proofs folder. Extracted/ is replaced wholesale (it is generated)."""
    if extracted_rel(m).endswith("Extracted"):
        shutil.rmtree(proj / extracted_rel(m), ignore_errors=True)
    mirror(local, proj, delete=False)


def render_lakefile(proj: Path):
    """lakefile.lean.tmpl -> lakefile.lean with the pinned Aeneas commit. Requiring Aeneas from git
    (not the local release path) keeps .lake/packages identical across sessions, so one cached
    tarball serves every Rust library."""
    t = proj / "lakefile.lean.tmpl"
    if t.exists():
        (proj / "lakefile.lean").write_text(t.read_text().replace("{{aeneas_commit}}", versions()["aeneas"]["commit"]))
    (proj / "lean-toolchain").write_text(f"leanprover/lean4:v{versions()['lean']['version']}\n")


# Lean 4.35 lake output: "warning: Demo/Proofs.lean:10:2: declaration uses `sorry`" (older: 'sorry').
SORRY_RE = re.compile(r"^(?:warning: )?(.+?\.lean):(\d+):\d+: (?:warning: )?declaration uses [`']sorry[`']", re.M)
ERR_RE = re.compile(r"^(?:error: (.+?\.lean):(\d+):\d+:|(.+?\.lean):(\d+):\d+: error)", re.M)
THM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+)?(theorem|lemma)\s+([^\s:({\[]+)", re.M)


def lean_theorems(proj, m):
    """Hand-written theorems: everything under the proof dirs except generated code."""
    out = []
    gen = (proj / extracted_rel(m)).resolve()
    for d in theorem_dirs(m):
        for f in sorted((proj / d).rglob("*.lean")):
            if f.resolve().is_relative_to(gen) or ".lake" in f.parts:
                continue
            lines = f.read_text().splitlines()
            for i, l in enumerate(lines, 1):
                mt = THM_RE.match(l)
                if mt:
                    out.append({"name": mt.group(2), "file": str(f.relative_to(proj)), "line": i})
    return out


STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_FILE = "VpipeAxiomAudit.lean"
AUDIT_LEAN = """import Lean
{imports}
open Lean

#eval show CoreM Unit from do
  let env <- getEnv
  let mods : List Name := [{mods}]
  for (n, ci) in env.constants.map₁.toList do
    if ci.isTheorem then
      match env.getModuleIdxFor? n with
      | some idx =>
        if mods.contains env.header.moduleNames[idx.toNat]! then
          let axs <- collectAxioms n
          IO.println s!"AXAUDIT\t{{n}}\t{{",".intercalate (axs.toList.map toString)}}"
      | none => pure ()
"""


def audit_axioms(proj, thms):
    """`#print axioms` equivalent (Lean.collectAxioms) for every hand-written theorem, run after a
    successful build. Returns {full theorem name: [axioms]} or None if the audit could not run."""
    files = sorted({t["file"] for t in thms})
    mods = [f[:-5].replace("/", ".") for f in files]
    if not mods:
        return {}
    (proj / AUDIT_FILE).write_text(AUDIT_LEAN.format(
        imports="\n".join(f"import {x}" for x in mods), mods=", ".join(f"`{x}" for x in mods)))
    try:
        r = sh(["lake", "env", "lean", AUDIT_FILE], cwd=proj, check=False, capture=True, timeout=3600)
    finally:
        (proj / AUDIT_FILE).unlink(missing_ok=True)
    out = (r.stdout or "") + (r.stderr or "")
    found = {}
    for line in out.splitlines():
        if line.startswith("AXAUDIT\t"):
            _, name, axs = (line.split("\t") + [""])[:3]
            found[name] = sorted(a for a in axs.split(",") if a)
    if r.returncode != 0 or not found:
        log("axiom audit failed:", out[-1500:])
        return None
    return found


def prove_lean(m, proj):
    restored = restore_lake_packages(proj)
    if not restored:
        # On an open network mathlib's own cache works and saves hours; harmless if blocked.
        sh(["lake", "exe", "cache", "get"], cwd=proj, check=False, capture=True, timeout=3600)
    t0 = dt.datetime.now()
    r = sh(["lake", "build"], cwd=proj, check=False, capture=True, timeout=6 * 3600)
    out = r.stdout + r.stderr
    if not restored:
        save_lake_packages(proj)  # built mathlib from source: publish it so nobody repeats that
        share_lake_packages(proj)  # and let the next project on this machine reuse it
    thms = lean_theorems(proj, m)
    # Aeneas writes `sorry` bodies for items it could not translate; those sit in generated code and
    # are already listed as "Skipped". Only sorries in hand-written files count against the proofs.
    gen = (proj / extracted_rel(m)).resolve()
    all_sorry = [(f, int(l)) for f, l in SORRY_RE.findall(out)]
    in_gen = [x for x in all_sorry if (proj / x[0]).resolve().is_relative_to(gen)]
    sorry_at = {(Path(f).name, l) for f, l in all_sorry if (f, l) not in in_gen}
    errors = sorted({f"{Path(f or f2).name}:{l or l2}" for f, l, f2, l2 in ERR_RE.findall(out)})
    audit = audit_axioms(proj, thms) if r.returncode == 0 and thms else {}
    for t in thms:
        if (Path(t["file"]).name, t["line"]) in sorry_at:
            t["status"] = "sorry"
        elif r.returncode:
            t["status"] = "error"
        elif audit is None:
            t["status"] = "unaudited"  # build passed but axioms unknown: never report as proved
        else:
            # full names carry namespaces/private prefixes, so match on the last components
            axs = [set(a) for n, a in audit.items() if n == t["name"] or n.endswith("." + t["name"])]
            if not axs:
                t["status"] = "unaudited"
                continue
            extra = sorted(set().union(*axs) - STD_AXIOMS)
            t["axioms"] = extra
            t["status"] = "sorry" if "sorryAx" in extra else "nonstandard-axioms" if extra else "proved"
    bad = sum(t["status"] == "nonstandard-axioms" for t in thms)
    unaudited = sum(t["status"] == "unaudited" for t in thms)
    replay = kernel_replay(proj, m) if r.returncode == 0 else None
    return {"ok": r.returncode == 0 and not bad and not unaudited, "seconds": (dt.datetime.now() - t0).seconds,
            "replay": replay,
            "theorems": thms, "proved": sum(t["status"] == "proved" for t in thms),
            "total": len(thms), "generated_sorries": len(in_gen), "sorries": max(len(sorry_at), sum(t["status"] == "sorry" for t in thms)),
            "axiom_thms": bad, "unaudited": unaudited, "errors": errors, "log": out[-8000:]}


def lean_search_path(proj):
    """LEAN_PATH for a built project, found on disk. `lake env` is avoided on purpose: when packages
    look out of date it runs mathlib's `cache get`, which hangs where the cache server is blocked."""
    roots = [proj / ".lake/build/lib/lean"]
    pk = proj / ".lake/packages"
    if pk.exists():
        for d in sorted(pk.iterdir()):
            roots += sorted(x for x in d.rglob("build/lib/lean") if ".lake/packages" not in str(x.relative_to(d)))
    return ":".join(str(x) for x in roots if x.is_dir())


def kernel_replay(proj, m):
    """Second check of every compiled module of the entry: Lean's `leanchecker` (lean4checker, part
    of the toolchain since v4.28) replays each declaration through the kernel from the .olean files."""
    lib = proj / ".lake/build/lib/lean" / module_name(m)
    mods = sorted(str(f.relative_to(proj / ".lake/build/lib/lean"))[:-6].replace("/", ".") for f in lib.rglob("*.olean"))
    top = proj / ".lake/build/lib/lean" / f"{module_name(m)}.olean"
    if top.exists():
        mods.insert(0, module_name(m))
    if not mods:
        return {"ok": False, "modules": 0, "log": "no compiled modules found"}
    tc = Path.home() / ".elan/toolchains" / f"leanprover--lean4---v{versions()['lean']['version']}" / "bin"
    exe = tc / "leanchecker"
    if not exe.exists():
        return {"ok": False, "modules": len(mods), "log": f"{exe} missing"}
    t0 = dt.datetime.now()
    r = sh([str(exe), *mods], cwd=proj, check=False, capture=True, timeout=6 * 3600,
           env={"LEAN_PATH": lean_search_path(proj), "PATH": f"{tc}:" + os.environ.get("PATH", "")})
    out = (r.stdout or "") + (r.stderr or "")
    ok = r.returncode == 0 and "found a problem" not in out
    return {"ok": ok, "tool": "leanchecker", "modules": len(mods), "seconds": (dt.datetime.now() - t0).seconds,
            "log": out[-3000:]}


# ---------------------------------------------------------------- frama-c
ACSL_RE = re.compile(r"/\*@.*?\*/|//@[^\n]*", re.S)


def annotation_only(src, overlay):
    """Annotated copies must equal upstream once ACSL is stripped (inih's strip_acsl check), so the
    proven code is the shipped code. Returns the overlay files that differ."""
    bad = []
    for f in sorted(overlay.rglob("*.[ch]")):
        up = src / f.relative_to(overlay)
        norm = lambda t: [l.rstrip() for l in ACSL_RE.sub("", t).splitlines() if l.strip()]
        if up.exists() and norm(f.read_text(errors="replace")) != norm(up.read_text(errors="replace")):
            bad.append(str(f.relative_to(overlay)))
    return bad


def prove_framac(m, src, proj, mutant=None, tag="annotated", clean=False, only=None):
    """Frama-C WP on the pinned C files with ACSL from the entry.
    Annotations come from proofs/<lib>/src/ (copies of upstream files) and/or [framac] annotate, a
    script run as `python3 -I <script> <pristine dir> <out dir>` that writes annotations into the copy
    (Neovim thread: keeps big files reviewable as a script). Either way the annotated files must
    equal upstream once ACSL is stripped.
    [framac] per_function = true runs WP once per function, with [framac.function.<name>] wp_args /
    cpp_args added, and merges the goals (Neovim: different functions need different options)."""
    v = versions()["framac"]
    f = m.get("framac", {})
    tree = WORK / m["name"] / tag
    shutil.rmtree(tree, ignore_errors=True)
    shutil.copytree(src, tree, ignore=shutil.ignore_patterns(".git"))
    if (proj / "src").exists():
        shutil.copytree(proj / "src", tree, dirs_exist_ok=True)
    t0 = dt.datetime.now()
    if f.get("annotate"):
        r = sh([sys.executable, "-I", str(proj / f["annotate"]), str(src), str(tree)], cwd=proj, check=False, capture=True,
               timeout=3600)
        if r.returncode != 0:
            return {"ok": False, "stage": "annotate", "proved": 0, "total": 0, "failed": [], "per_function": {},
                    "annotation_diffs": [], "seconds": 0, "log": ((r.stdout or "") + (r.stderr or ""))[-4000:]}
    if mutant:
        apply_mutant(tree, mutant)
    # Tool patches (Neovim): statements rewritten so WP can read them. The annotated code must equal
    # upstream with exactly these rewrites, and each rewrite needs an equivalence harness that passes.
    ref, tps = src, []
    if f.get("tool_patch"):
        ref = WORK / m["name"] / f"upstream-tool-patched-{tag}"
        shutil.rmtree(ref, ignore_errors=True)
        shutil.copytree(src, ref, ignore=shutil.ignore_patterns(".git"))
        for tp in f["tool_patch"]:
            rec = {"id": tp.get("id"), "file": tp.get("file")}
            try:
                apply_mutant(ref, {"file": tp["file"], "find": tp["original"], "replace": tp["rewritten"]})
                rec.update(run_cbmc({"harness": tp.get("harness", ""), "harness_files": tp.get("harness_files", [])}, tree))
            except (KeyError, ValueError) as e:
                rec.update(ok=False, why=str(e))
            tps.append(rec)
    honesty = annotation_only(ref, proj / "src") if (proj / "src").exists() else []
    if f.get("annotate") and not mutant:
        honesty += [x for x in annotation_only_files(ref, tree, f.get("files", [])) if x not in honesty]
    wp_args = f.get("wp_args", ["-wp-rte", "-wp-literals"])
    session = WORK / m["name"] / f"wp-session-{tag}"
    if clean or mutant:  # no cached proof results: clean runs and planted-bug runs prove from scratch
        shutil.rmtree(session, ignore_errors=True)
    files = [str(tree / x) for x in f.get("files", [])]

    def wp(fns, extra_cpp=(), extra_wp=(), name="all"):
        rep_ = WORK / m["name"] / f"wp-{tag}-{name}.json"
        rep_.unlink(missing_ok=True)
        # Defaults from the inih and Neovim threads: -wp-literals (string literal contents, needed
        # for strchr(";#", c)); a WP session cache so re-runs only re-prove changed goals.
        cmd = ["frama-c", *f.get("cpp_args", []), *extra_cpp, *files, "-wp", *wp_args, *extra_wp,
               "-wp-prover", ",".join(v["provers"]), "-wp-timeout", str(f.get("wp_timeout", v["wp_timeout"])),
               "-wp-session", str(session), "-wp-cache", "update", "-wp-report-json", str(rep_)]
        if fns:
            cmd += ["-wp-fct", ",".join(fns)]
        r = sh(cmd, cwd=tree, check=False, capture=True, timeout=6 * 3600)
        return r, (json.loads(rep_.read_text()) if rep_.exists() else [])

    fns = list(only or f.get("functions", []))
    runs = []
    if f.get("per_function"):
        names = fns or [x["name"] for x in scan_c_functions(tree, f.get("files", []))]
        for n in names:
            o = f.get("function", {}).get(n, {})
            r, goals_ = wp([n], o.get("cpp_args", []), o.get("wp_args", []), n)
            runs.append((n, r, goals_))
    else:
        r, goals_ = wp(fns)
        runs.append(("all", r, goals_))
    goals = [g for _, _, gs in runs for g in gs]
    failed = [{"goal": g["goal"], "function": g.get("function"), "line": g.get("line"),
               "verdict": g.get("verdict")} for g in goals if not g.get("passed")]
    per_fn = {}
    for g in goals:
        e = per_fn.setdefault(g.get("function") or "(global)", {"proved": 0, "total": 0})
        e["total"] += 1
        e["proved"] += 1 if g.get("passed") else 0
    rc_bad = [n for n, r, _ in runs if r.returncode != 0]
    return {"ok": not rc_bad and not failed and bool(goals) and not honesty and all(t["ok"] for t in tps),
            "annotation_diffs": honesty, "wp_args": wp_args, "tool_patches": tps, "runs": len(runs), "failed_runs": rc_bad[:50],
            "per_function": dict(sorted(per_fn.items())),
            "seconds": (dt.datetime.now() - t0).seconds, "proved": len(goals) - len(failed),
            "total": len(goals), "failed": failed[:200],
            "functions": sorted({g.get("function") for g in goals if g.get("function")}),
            "log": "\n".join(((r.stdout or "") + (r.stderr or ""))[-8000 // max(1, len(runs)):] for _, r, _ in runs[-5:])}


def annotation_only_files(src, tree, files):
    """Listed files in the annotated tree must equal upstream once ACSL is stripped."""
    bad = []
    norm = lambda t: [l.rstrip() for l in ACSL_RE.sub("", t).splitlines() if l.strip()]
    for rel in files:
        a, b = tree / rel, src / rel
        if a.exists() and b.exists() and norm(a.read_text(errors="replace")) != norm(b.read_text(errors="replace")):
            bad.append(rel)
    return bad


# ---------------------------------------------------------------- agent stage
def agent(m, proj, last, budget):
    prompt = (ROOT / "templates/prompts" / f"{m['tool']}.md").read_text()
    ctx = {"lib": m["name"], "proj": str(proj), "manifest": json.dumps(m, indent=1),
           "last": json.dumps({k: v for k, v in last.items() if k != "log"}, indent=1)[:12000],
           "log": last.get("prove", {}).get("log", "")[-4000:], "notes": str(NOTES),
           "src": str(WORK / m["name"] / "src")}
    for k, val in ctx.items():
        prompt = prompt.replace("{{" + k + "}}", val)
    tools = ("Read Edit Write Glob Grep Bash(lake:*) Bash(lean:*) Bash(frama-c:*) Bash(cat:*) "
             "Bash(ls:*) Bash(grep:*) Bash(rg:*) Bash(head:*) Bash(tail:*) Bash(git diff:*)")
    sh(["claude", "-p", prompt, "--max-turns", str(budget), "--permission-mode", "acceptEdits",
        "--allowedTools", tools, "--add-dir", str(WORK / m["name"])], cwd=proj, check=False,
       timeout=4 * 3600)



# ---------------------------------------------------------------- function inventory
# Yerin's rule (2026-10-24): a library is finished only when EVERY function in it is verified or
# has a verified fix. The pipeline scans the pinned source for every function, decides each one's
# status from evidence, and never reports "complete" while any function is open.
# Human input lives in libraries/<lib>/functions.toml:
#   [[function]]
#   id = "src/baseline.rs:update_fast_16"     # as listed in results/<lib>/latest.json
#   theorems = ["update_fast_16_spec"]        # Lean: proved theorems that specify it (optional;
#                                             # otherwise found automatically)
#   lean = "crc32fast.baseline.update_fast_16" # Lean def it was extracted to (optional; otherwise
#                                             # matched by source line, then by unique name)
#   status = "fixed"                          # only for a verified fix:
#   fix = "patches/fix-overflow.patch"        #   the patch that fixes it (applied before proving)
#   note = "..."
#   status = "open"; why = "..."              # evidence exists but does not cover the real code yet
# Allowed statuses: verified, fixed, open. There is deliberately no "out of scope".

RUST_SKIP_DIRS = {"tests", "benches", "examples", "target", "fuzz"}
RUST_FN_RE = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:async\s+)?(?:unsafe\s+)?"
                        r"(?:extern\s+\"[^\"]*\"\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)")
RUST_IMPL_RE = re.compile(r"^\s*(?:unsafe\s+)?impl\b(?:<[^{]*?>)?\s*(.*?)\s*(?:where\b.*)?\{?\s*$")
RUST_TRAIT_RE = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:unsafe\s+)?trait\s+([A-Za-z_][A-Za-z0-9_]*)")


def _strip_rust(line):
    line = re.sub(r'"(?:\\.|[^"\\])*"', '""', line)
    line = re.sub(r"'(?:\\.|[^'\\])'", "''", line)
    return line.split("//")[0]


def scan_rust_functions(crate: Path):
    """Every `fn` in the crate's src/ (with its impl/trait), skipping #[cfg(test)] modules.
    Functions behind cfg(...) for other targets are included on purpose: they count too."""
    out = []
    for f in sorted((crate / "src").rglob("*.rs")) if (crate / "src").exists() else []:
        if RUST_SKIP_DIRS & set(f.relative_to(crate).parts):
            continue
        depth, ctx, test_until, pending_test, pending_ctx = 0, [], None, False, None
        in_block_comment = False
        for i, raw in enumerate(f.read_text(errors="replace").splitlines(), 1):
            line = raw
            if in_block_comment:
                if "*/" not in line:
                    continue
                line, in_block_comment = line.split("*/", 1)[1], False
            if "/*" in line and "*/" not in line.split("/*", 1)[1]:
                line, in_block_comment = line.split("/*", 1)[0], True
            code = _strip_rust(line)
            if re.search(r"#\[cfg\(test\)\]", code):
                pending_test = True
            if test_until is None:
                mt = RUST_FN_RE.match(code)
                if mt:
                    owner = next((c[1] for c in reversed(ctx) if c[1]), "")
                    name = f"{owner}::{mt.group(1)}" if owner else mt.group(1)
                    out.append({"id": f"{f.relative_to(crate)}:{name}", "file": str(f.relative_to(crate)),
                                "line": i, "name": mt.group(1)})
                mi, mtr = RUST_IMPL_RE.match(code), RUST_TRAIT_RE.match(code)
                if mi:
                    tgt = mi.group(1)
                    tgt = re.sub(r"<.*>", "", tgt.split(" for ")[-1]).strip() if " for " in tgt else re.sub(r"<.*>", "", tgt).strip()
                    owner = (re.sub(r"<.*>", "", mi.group(1).split(" for ")[0]).strip() + " for " + tgt) if " for " in mi.group(1) else tgt
                    pending_ctx = owner
                elif mtr:
                    pending_ctx = mtr.group(1)
            for ch in code:
                if ch == "{":
                    depth += 1
                    if pending_test and test_until is None:
                        test_until, pending_test = depth, False
                    ctx.append((depth, pending_ctx))
                    pending_ctx = None
                elif ch == "}":
                    if test_until is not None and depth == test_until:
                        test_until = None
                    depth -= 1
                    while ctx and ctx[-1][0] > depth:
                        ctx.pop()
            if pending_test and code.strip() and not code.strip().startswith("#") and "{" not in code and ";" in code:
                pending_test = False  # #[cfg(test)] on a single item like `use`
    return out


C_FN_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*\(([^;{}]*)\)\s*(?:\{|$)")


def scan_c_functions(tree: Path, files):
    """Every function definition (not prototype) in the listed C files."""
    out = []
    for rel in files:
        f = tree / rel
        if not f.exists():
            continue
        text = f.read_text(errors="replace")
        text = re.sub(r"/\*.*?\*/", lambda mm: "\n" * mm.group(0).count("\n"), text, flags=re.S)
        text = re.sub(r"//[^\n]*", "", text)
        depth, buf, start = 0, "", 1
        for i, line in enumerate(text.splitlines(), 1):
            if depth == 0:
                if not buf.strip():
                    start = i
                buf += " " + line
                if "{" in line:
                    head = buf.split("{")[0]
                    mt = C_FN_RE.search(head + "{")
                    if mt and not re.match(r"\s*(?:if|for|while|switch|return|sizeof)\b", mt.group(1)) and \
                            not re.search(r"\b(?:struct|union|enum)\s+\w*\s*$", head.split("(")[0]) and "=" not in head.split("(")[0]:
                        out.append({"id": f"{rel}:{mt.group(1)}", "file": rel, "line": start, "name": mt.group(1)})
                    buf = ""
                elif ";" in line or line.strip().startswith("#"):
                    buf = ""
            for ch in line:
                depth += (ch == "{") - (ch == "}")
    return out


AENEAS_DOC_RE = re.compile(r"/-- \[([^\]]+)\]:\s*\n\s*Source: '([^']+)', lines (\d+):\d+-(\d+):\d+(.*?)-/\s*\n(?:@\[[^\n]*\]\s*\n)*"
                           r"(?:noncomputable\s+)?(?:partial\s+)?(?:def|theorem|opaque)\s+(\S+)", re.S)


def aeneas_defs(ext: Path):
    """(file, start line) -> Lean def name, for top-level functions in Aeneas output."""
    out = {}
    for f in sorted(ext.glob("Funs*.lean")):
        for path, src, a, b, rest, name in AENEAS_DOC_RE.findall(f.read_text()):
            out.setdefault((src, int(a)), name)
    return out


def theorem_statements(proj, m):
    """name -> statement text (from `theorem` to `:=`) for hand-written theorems."""
    out = {}
    for t in lean_theorems(proj, m):
        lines = (proj / t["file"]).read_text().splitlines()[t["line"] - 1:t["line"] + 40]
        stmt = "\n".join(lines).split(":=")[0]
        out[t["name"]] = stmt
    return out


def _unique_ids(fns):
    """Same name twice (cfg variants, several `From` impls): add the line to the id, before
    functions.toml overrides are matched, so each one can be addressed."""
    seen = {}
    for f in fns:
        seen[f["id"]] = seen.get(f["id"], 0) + 1
    for f in fns:
        if seen[f["id"]] > 1:
            f["id"] = f"{f['id']}@L{f['line']}"
    return fns


def function_inventory(m, tree, proj, res):
    lib = m["name"]
    overrides = {}
    of = proj / "functions.toml"
    if of.exists():
        for e in tomllib.loads(of.read_text()).get("function", []):
            overrides[e["id"]] = e
    if m["tool"] == "lean-aeneas":
        # Count the functions of the real upstream crate, even when proofs run on a patched copy or
        # a model crate (semver, Helix). [functions] crate_dir overrides where upstream code lives.
        crate = tree / (m.get("functions", {}).get("crate_dir") or m.get("extract", {}).get("crate_dir", "."))
        if not (crate / "src").exists():  # extract crate_dir is a model crate added by a patch
            crate = tree
        fns = _unique_ids(scan_rust_functions(crate))
        defs = aeneas_defs(proj / extracted_rel(m))
        thm_status = {t["name"]: t["status"] for t in res.get("prove", {}).get("theorems", [])}
        stmts = theorem_statements(proj, m) if thm_status else {}
        for fn in fns:
            near = [(abs(l - fn["line"]), name) for (src, l), name in defs.items()
                    if src == fn["file"] and abs(l - fn["line"]) <= 3]
            if not near:  # patched or model code: lines moved, so fall back to a unique name match
                same = [name for (src_, l), name in defs.items() if name.split(".")[-1] == fn["name"]]
                near = [(0, same[0])] if len(same) == 1 else []
            ov = overrides.get(fn["id"], {})
            # functions.toml may name the Lean def when line/name matching fails (patched code moved lines).
            fn["lean"] = ov.get("lean") or (min(near)[1] if near else None)
            evidence = ov.get("theorems")
            if evidence is None and fn["lean"]:
                full = fn["lean"]
                tail = full.split(".")[-1]
                tail_unique = sum(1 for n in defs.values() if n.split(".")[-1] == tail) == 1
                pats = [re.escape(full)] + ([r"(?<![\w.])" + re.escape(tail) + r"(?![\w])"] if tail_unique else [])
                evidence = [n for n, st in stmts.items() if any(re.search(p_, st) for p_ in pats)]
            evidence = evidence or []
            proved = [e for e in evidence if thm_status.get(e) == "proved"]
            fn["theorems"] = evidence
            if not fn["lean"]:
                fn["status"], fn["why"] = "open", "not extracted (unsupported by Aeneas or excluded by cfg)"
            elif ov.get("status") == "open":  # a human says the evidence does not cover the real code yet
                fn["status"], fn["why"] = "open", ov.get("why", "marked open in functions.toml")
            elif evidence and len(proved) == len(evidence):
                fn["status"] = "fixed" if ov.get("status") == "fixed" and ov.get("fix") else "verified"
            else:
                fn["status"] = "open"
                fn["why"] = "no theorem about it" if not evidence else f"theorems not proved: {sorted(set(evidence) - set(proved))}"
            if ov.get("note"):
                fn["note"] = ov["note"]
    else:
        files = m.get("framac", {}).get("files", [])
        fns = _unique_ids(scan_c_functions(tree, files))
        annotated = WORK / lib / "annotated"
        pf = res.get("prove", {}).get("per_function", {})
        for fn in fns:
            ov = overrides.get(fn["id"], {})
            g = pf.get(fn["name"], {"proved": 0, "total": 0})
            src_text = (annotated / fn["file"]).read_text(errors="replace") if (annotated / fn["file"]).exists() else ""
            # A contract with an ensures clause right before the definition (or on a prototype).
            has_contract = bool(re.search(r"/\*@(?:(?!\*/).)*\bensures\b(?:(?!\*/).)*\*/\s*(?:[\w\s\*]+?)\b"
                                          + re.escape(fn["name"]) + r"\s*\(", src_text, re.S))
            fn["goals"] = g
            if ov.get("verified_by") == "cbmc":
                # A bounded model-checking harness the pipeline re-runs. Must use --unwinding-assertions
                # (so the bound is checked, not assumed); the label stays "bounded" (standard: does not
                # count toward admission; such entries stay under candidates/).
                fn["cbmc"] = run_cbmc(ov, tree)
                if fn["cbmc"]["ok"]:
                    fn["status"] = "fixed" if ov.get("status") == "fixed" and ov.get("fix") else "verified"
                    fn["bounds"] = ov.get("bounds", "not recorded")
                else:
                    fn["status"], fn["why"] = "open", f"CBMC harness: {fn['cbmc']['why']}"
            elif g["total"] and g["proved"] == g["total"] and has_contract:
                fn["status"] = "fixed" if ov.get("status") == "fixed" and ov.get("fix") else "verified"
            else:
                fn["status"] = "open"
                fn["has_ensures"] = has_contract
                fn["why"] = ("no ensures contract" if not has_contract else
                             f"{g['total'] - g['proved']} of {g['total']} WP goals open" if g["total"] else "no WP goals")
            if ov.get("note"):
                fn["note"] = ov["note"]
    for fn in fns:  # work queue: who is on it (`vpipe take`); never changes the status
        ov = overrides.get(fn["id"], {})
        if ov.get("claimed_by") and fn["status"] == "open":
            fn["claimed_by"] = ov["claimed_by"]
    unknown = sorted(set(overrides) - {f["id"] for f in fns})
    seen = {}
    for f in fns:  # same name twice (cfg variants, several `From` impls): add the line to the id
        seen[f["id"]] = seen.get(f["id"], 0) + 1
    for f in fns:
        if seen[f["id"]] > 1:
            f["id"] = f"{f['id']}@L{f['line']}"
    counts = {k: sum(f["status"] == k for f in fns) for k in ("verified", "fixed", "open")}
    return {"total": len(fns), **counts, "complete": bool(fns) and counts["open"] == 0,
            "functions": fns, "overrides_not_found": unknown}


def run_cbmc(ov, tree):
    cmd = ov.get("harness", "")
    if not cmd:
        return {"ok": False, "why": "verified_by = cbmc needs harness = \"<command>\""}
    if "--unwinding-assertions" not in cmd and "--unwinding-assertions" not in " ".join(ov.get("harness_args", [])):
        return {"ok": False, "why": "harness must pass --unwinding-assertions", "cmd": cmd}
    r = sh(cmd.format(tree=tree), cwd=tree, check=False, capture=True, timeout=6 * 3600)
    out = (r.stdout or "") + (r.stderr or "")
    ok = r.returncode == 0 and "VERIFICATION SUCCESSFUL" in out
    # complete = true claims the harness covers every input (straight-line or fixed loops, inputs over
    # their whole type, no size limits). Machine part: listed harness files contain no __CPROVER_assume.
    # The reviewer checks the rest of the claim.
    assumes = []
    for hf in ov.get("harness_files", []):
        t = (Path(str(tree)) / hf) if not Path(hf).is_absolute() else Path(hf)
        if t.exists() and "__CPROVER_assume" in t.read_text(errors="replace"):
            assumes.append(hf)
    complete = bool(ov.get("complete")) and bool(ov.get("harness_files")) and not assumes
    return {"ok": ok, "cmd": cmd, "why": "" if ok else f"exit {r.returncode}, no VERIFICATION SUCCESSFUL",
            "complete": complete, "assume_in": assumes, "tail": out[-1500:]}


# ---------------------------------------------------------------- work queue
# Many sessions on one big library (Neovim): `vpipe next` lists open functions whose callees are
# already verified (so their specs can be used), `vpipe take` records who works on one.

def call_graph(m, tree, fns):
    """{function id: [ids of library functions it calls]}, by name, from the source text."""
    by_file = {}
    for f in fns:
        by_file.setdefault(f["file"], []).append(f)
    names = {}
    for f in fns:
        names.setdefault(f["name"], []).append(f["id"])
    graph = {}
    for rel, fs in by_file.items():
        p = tree / rel
        if not p.exists():
            continue
        lines = p.read_text(errors="replace").splitlines()
        fs = sorted(fs, key=lambda f: f["line"])
        for i, f in enumerate(fs):
            end = fs[i + 1]["line"] - 1 if i + 1 < len(fs) else len(lines)
            body = "\n".join(lines[f["line"]:end])
            graph[f["id"]] = sorted({cid for n, ids in names.items() if n != f["name"]
                                     and re.search(r"(?<![\w.])" + re.escape(n) + r"\s*\(", body) for cid in ids})
    return graph


def next_functions(lib, n=20):
    m = manifest(lib)
    res = load_json(results_dir(lib) / "latest.json")
    if not res or not res.get("functions"):
        raise SystemExit(f"no function inventory for {lib}; run it first")
    fns = res["functions"]["functions"]
    tree = WORK / m["name"] / "src"
    graph = call_graph(m, tree, fns)
    status = {f["id"]: f["status"] for f in fns}
    out = []
    for f in fns:
        if f["status"] != "open" or f.get("claimed_by"):
            continue
        callees = graph.get(f["id"], [])
        waiting = [c for c in callees if status.get(c) == "open"]
        out.append({"id": f["id"], "why": f.get("why", ""), "callees": len(callees), "waiting_on": waiting[:10]})
    out.sort(key=lambda x: (len(x["waiting_on"]), x["callees"], x["id"]))
    return out[:n]


def take(lib, fn_id, by):
    """Record claimed_by in functions.toml (adds an entry if the function has none)."""
    m = manifest(lib)
    of = proof_dir(lib, m) / "functions.toml"
    text = of.read_text() if of.exists() else "# Per-function evidence and fixes; see vpipe.py function inventory.\n"
    ents = tomllib.loads(text).get("function", [])
    cur = next((e for e in ents if e["id"] == fn_id), None)
    if cur and cur.get("claimed_by") and cur["claimed_by"] != by:
        raise SystemExit(f"{fn_id} is already taken by {cur['claimed_by']}")
    stamp = f"{by}, {now()}"
    if cur:
        blocks = re.split(r"(?m)^(?=\[\[function\]\])", text)
        for i, b in enumerate(blocks):
            if re.search(r'(?m)^id\s*=\s*"' + re.escape(fn_id) + '"', b):
                b = re.sub(r"(?m)^claimed_by\s*=.*\n?", "", b)
                blocks[i] = re.sub(r'(?m)^(id\s*=\s*"' + re.escape(fn_id) + '".*)$', r"\1\nclaimed_by = " + json.dumps(stamp), b, count=1)
        text = "".join(blocks)
    else:
        text = text.rstrip("\n") + f'\n\n[[function]]\nid = {json.dumps(fn_id)}\nclaimed_by = {json.dumps(stamp)}\n'
    tomllib.loads(text)
    of.write_text(text)
    return {"id": fn_id, "claimed_by": stamp}


# ---------------------------------------------------------------- build variants
# Some crates put functions behind different cfgs (target, features), so no single Charon run sees
# them all. Each [[variant]] is its own Lean project, assembled by overlay (crc32fast thread):
#   libraries/<lib>/common/            base project (lakefile.lean.tmpl, <Module>/*.lean)
#   libraries/<lib>/variants/<name>/   files that replace or add to common/ (e.g. External/ models)
# Every variant keeps the same module names (<Module>.Extracted.Funs), so shared proofs need no edits.
#   [[variant]]
#   name = "x86_64-std"
#   cargo_args = ["--target", "x86_64-unknown-linux-gnu"]   # replaces [extract].cargo_args
#   sysroot_default = false
#   patches = ["patches/aarch64-loop.patch"]                # on top of [patches]
#   aeneas_args = []
# A function counts as verified if any variant proves it.

def variants(m):
    return m.get("variant") or []


def variant_manifest(m, v):
    x = dict(m.get("extract", {}))
    for k in ("cargo_args", "sysroot_default", "aeneas_args", "charon_args", "crate_dir", "cargo_lock"):
        if k in v:
            x[k] = v[k]
    mv = dict(m)
    mv["extract"] = x
    mv["_variant"] = v["name"]
    return mv


def variant_tree(m, v, src, proj):
    """The source tree for one variant: the prepared tree, plus that variant's extra patches."""
    if not v.get("patches"):
        return src, None
    t = WORK / m["name"] / f"tree-{v['name']}"
    shutil.rmtree(t, ignore_errors=True)
    shutil.copytree(src, t, ignore=shutil.ignore_patterns(".git", "target"))
    for pf in v["patches"]:
        r = sh(["patch", "-s", "-p1", "-d", str(t / m.get("patches", {}).get("dir", ".")), "-i", str(proj / pf)],
               check=False, capture=True)
        if r.returncode != 0:
            return t, f"variant {v['name']}: patch {pf} failed: {(r.stdout + r.stderr)[-1500:]}"
    return t, None


def run_variants(m, src, proj, extract_only, clean=False):
    """Extract and prove each variant in its own local project; return per-variant results."""
    per = {}
    common = proj / "common"
    for v in variants(m):
        mv = variant_manifest(m, v)
        local = WORK / m["name"] / "variants" / v["name"]
        mirror(common, local, delete=True)
        if clean:
            shutil.rmtree(local / ".lake/build", ignore_errors=True)
        vdir = proj / "variants" / v["name"]
        if vdir.exists():
            shutil.copytree(vdir, local, dirs_exist_ok=True, ignore=shutil.ignore_patterns(".lake"))
        tree, err = variant_tree(m, v, src, proj)
        if err:
            per[v["name"]] = {"extract": {"ok": False, "stage": "patch", "log": err}}
            continue
        ex = extract_rust(mv, tree, local)
        pr = prove_lean(mv, local) if ex["ok"] and not extract_only else None
        per[v["name"]] = {"extract": ex, "prove": pr, "local": str(local)}
        # Keep generated code and first-time External models visible in the variant folder.
        for rel in (extracted_rel(mv), externals_rel(mv)):
            if (local / rel).exists():
                shutil.rmtree(vdir / rel, ignore_errors=True) if rel.endswith("Extracted") else None
                shutil.copytree(local / rel, vdir / rel, dirs_exist_ok=True)
    return per


def merge_variants(per):
    """One summary over all variants for SUMMARY.md; details stay under res["variants"]."""
    exs = [r["extract"] for r in per.values()]
    prs = [r["prove"] for r in per.values() if r.get("prove")]
    ex = {"ok": bool(exs) and all(e["ok"] for e in exs), "stage": "variants",
          "unsupported": [u for e in exs for u in e.get("unsupported", [])],
          "assumed_axioms": sorted({a for e in exs for a in e.get("assumed_axioms", [])}),
          "external_template_changes": [c for e in exs for c in e.get("external_template_changes", [])]}
    pr = None
    if prs:
        pr = {"ok": len(prs) == len(exs) and all(q["ok"] for q in prs),
              "proved": sum(q["proved"] for q in prs), "total": sum(q["total"] for q in prs),
              "sorries": sum(q["sorries"] for q in prs), "generated_sorries": sum(q.get("generated_sorries", 0) for q in prs),
              "axiom_thms": sum(q.get("axiom_thms", 0) for q in prs), "unaudited": sum(q.get("unaudited", 0) for q in prs),
              "errors": [e for q in prs for e in q.get("errors", [])][:50],
              "theorems": [dict(t, variant=n) for n, r in per.items() if r.get("prove") for t in r["prove"]["theorems"]]}
    return ex, pr


def merge_inventories(invs):
    """A function is verified (or fixed) if any variant proves it."""
    rank = {"verified": 2, "fixed": 2, "open": 0}
    best = {}
    for name, inv in invs.items():
        for f in inv["functions"]:
            f = dict(f, variant=name)
            cur = best.get(f["id"])
            if cur is None or rank[f["status"]] > rank[cur["status"]]:
                if cur is not None and f["status"] == "open":
                    continue
                best[f["id"]] = f
            elif cur["status"] == "open" and f["status"] == "open":
                cur["why"] = cur.get("why", "") + f"; {name}: {f.get('why', '')}"
    fns = sorted(best.values(), key=lambda f: (f["file"], f["line"]))
    counts = {k: sum(f["status"] == k for f in fns) for k in ("verified", "fixed", "open")}
    return {"total": len(fns), **counts, "complete": bool(fns) and counts["open"] == 0, "functions": fns,
            "overrides_not_found": sorted(set().union(*[set(i.get("overrides_not_found", [])) for i in invs.values()]))}

# ---------------------------------------------------------------- run
def prepare_source(m, src, proj, run_tests=True):
    """Apply proofs/<lib>/ patch files to a fresh copy of the pinned checkout, then run the
    manifest's [test] commands on it (upstream tests, differential tests). Returns (tree, info)."""
    patches = m.get("patches", {}).get("files", [])
    info = {"patches": patches, "tests": []}
    tree = src
    if patches:
        tree = WORK / m["name"] / "patched"
        shutil.rmtree(tree, ignore_errors=True)
        sub = m["patches"].get("subtree")  # copy only this folder (keeps it out of the workspace)
        shutil.copytree(src / sub if sub else src, tree / sub if sub else tree,
                        ignore=shutil.ignore_patterns(".git", "target"))
        for pf in patches:
            r = sh(["patch", "-s", "-p1", "-d", str(tree / m["patches"].get("dir", ".")), "-i", str(proj / pf)],
                   check=False, capture=True)
            if r.returncode != 0:
                info["error"] = f"patch {pf} failed: {(r.stdout + r.stderr)[-1500:]}"
                return tree, info
    for cmd in (m.get("test", {}).get("commands", []) if run_tests else []):
        # {src} = pristine upstream checkout, {tree} = patched tree, {proj} = proofs folder
        c = cmd.format(src=src, tree=tree, proj=proj)
        r = sh(c, cwd=tree, check=False, capture=True, timeout=3 * 3600)
        info["tests"].append({"cmd": cmd, "ok": r.returncode == 0, "tail": (r.stdout + r.stderr)[-1500:]})
        if r.returncode != 0:
            info["error"] = f"test failed: {cmd}"
            return tree, info
    return tree, info


def run(lib, use_agent=False, rounds=3, budget=60, extract_only=False, clean=False, functions=None):
    m = manifest(lib)
    tool = m["tool"]
    # Standard gate 5: success criteria come first. No proving until [scope].properties is written.
    if not extract_only and not m.get("scope", {}).get("properties"):
        raise SystemExit(f"{lib}: write [scope].properties (the success criteria) in vpipe.toml before proving; "
                         "`--extract-only` still works")
    setup("lean" if tool == "lean-aeneas" else "framac")
    src = fetch(m)
    proj = proof_dir(lib, m)
    if not proj.exists():
        raise SystemExit(f"{proj} missing; run `vpipe new {lib}` first")
    res = {"library": lib, "entry": entry_key(lib), "commit": m["commit"], "version": m.get("version"), "tool": tool,
           "started": now(), "pipeline_version": (ROOT / "VERSION").read_text().strip(),
           "toolchain": json.loads((VH / "installed.json").read_text()), "clean": clean,
           "toolchain_digest": toolchain_digest(tool), "container_digest": os.environ.get("VPIPE_CONTAINER_DIGEST"),
           "ci_run": os.environ.get("VPIPE_CI_RUN")}
    pristine = src
    res["archive_sha256"] = standards.archive_sha256(src, m["commit"])
    src, res["source"] = prepare_source(m, src, proj)
    if res["source"].get("error"):
        res["finished"] = now()
        write_result(lib, res)
        return res
    if variants(m) and tool == "lean-aeneas":
        per = run_variants(m, src, proj, extract_only, clean)
        res["variants"] = {n: {k: v for k, v in r.items() if k in ("extract", "prove")} for n, r in per.items()}
        res["extract"], pr = merge_variants(per)
        if pr:
            res["prove"] = pr
        invs = {n: function_inventory(variant_manifest(m, next(v for v in variants(m) if v["name"] == n)),
                                      pristine, Path(r["local"]), {"prove": r.get("prove") or {}})
                for n, r in per.items() if r.get("local") and r["extract"].get("ok")}
        if invs:
            res["functions"] = merge_inventories(invs)
        return finish(lib, m, res, proj, src, {n: Path(r["local"]) for n, r in per.items() if r.get("local")})
    for i in range(rounds if use_agent else 1):
        if tool == "lean-aeneas":
            # Build in a local copy: lake on the network mount is slow and fights other sessions.
            local = WORK / lib / "proj"
            mirror(proj, local, delete=True)
            if clean:  # rebuild every module of the entry; dependency oleans (mathlib) stay cached
                shutil.rmtree(local / ".lake/build", ignore_errors=True)
            res["extract"] = extract_rust(m, src, local)
            if not res["extract"]["ok"] or extract_only:
                sync_back(local, proj, m)
                break
            res["prove"] = prove_lean(m, local)
            # Copy hand-written work (and the fresh extraction) back to the shared folder.
            sync_back(local, proj, m)
        else:
            res["prove"] = prove_framac(m, src, proj, clean=clean, only=functions)
            if functions:
                res["partial"] = functions  # a quick check of some functions: never the entry's result
        p = res["prove"]
        done = p["ok"] and p.get("sorries", 0) == 0 and p["total"] > 0
        if done or not use_agent:
            break
        log(f"round {i + 1}: {p['proved']}/{p['total']} proved; handing to agent")
        agent(m, proj, res, budget)
    if res.get("prove") or res.get("extract", {}).get("ok"):
        res["functions"] = function_inventory(m, pristine, proj if tool != "lean-aeneas" else WORK / lib / "proj", res)
    return finish(lib, m, res, proj, src, {"main": WORK / lib / "proj"} if tool == "lean-aeneas" else {})


def finish(lib, m, res, proj, tree, locals_):
    """After proving: cross-checks, forbidden-construct scan, then the admission evaluation."""
    if res.get("prove") and not res.get("source", {}).get("error"):
        res["crosscheck"] = []
        for cmd in m.get("crosscheck", {}).get("commands", []):
            # {tree} = source tree that was proved, {proj} = entry folder, {build} = local Lean build
            c = cmd.format(tree=tree, proj=proj, build=next(iter(locals_.values()), proj))
            r = sh(c, cwd=tree, check=False, capture=True, timeout=3 * 3600)
            res["crosscheck"].append({"cmd": cmd, "ok": r.returncode == 0, "tail": (r.stdout + r.stderr)[-1500:]})
        res["forbidden"] = forbidden_scan(m, res, locals_)
    res["model_crate"] = model_crate(m, tree)
    res["finished"] = now()
    evaluate(lib, m, res, proj, write_card=True)
    write_result(lib, res)
    return res


def toolchain_digest(tool):
    """sha256 over the pinned versions and the bytes of the tools that ran. Equal digests = same
    toolchain. (The standard also wants a container digest; CI sets VPIPE_CONTAINER_DIGEST.)"""
    h = hashlib.sha256((ROOT / "toolchain/versions.toml").read_bytes())
    if tool == "lean-aeneas":
        lean_bin = Path.home() / ".elan/toolchains" / f"leanprover--lean4---v{versions()['lean']['version']}" / "bin"
        exes = [VH / "aeneas/aeneas", VH / "aeneas/charon", VH / "aeneas/charon-driver", lean_bin / "lean", lean_bin / "leanchecker"]
    else:
        exes = [Path(shutil.which(x) or "/nonexistent") for x in ("frama-c", "why3", *versions()["framac"]["provers"])]
    for e in exes:
        e = e.resolve() if e.exists() else e
        h.update(str(e.name).encode())
        if e.is_file():
            with open(e, "rb") as fh:
                for chunk in iter(lambda: fh.read(1 << 20), b""):
                    h.update(chunk)
        else:
            h.update(b"missing")
    return "sha256:" + h.hexdigest()


def model_crate(m, tree):
    """True when the proofs are about a crate that is not part of the pinned upstream source."""
    if m["tool"] != "lean-aeneas":
        return False
    if m.get("trust", {}).get("model_crate"):
        return True
    for x in [m.get("extract", {})] + [v for v in variants(m)]:
        cd = x.get("crate_dir")
        if cd and cd != "." and not (WORK / m["name"] / "src" / cd / "Cargo.toml").exists():
            return True
    return False


def forbidden_scan(m, res, locals_):
    if m["tool"] == "framac":
        return standards.forbidden_framac(WORK / m["name"] / "annotated", m.get("framac", {}).get("files", []),
                                          (res.get("prove") or {}).get("wp_args", []))
    listed = set(m.get("trust", {}).get("models", [])) | set(m.get("trust", {}).get("axioms", []))
    hits = []
    for name, local in locals_.items():
        if not local.exists():
            continue
        # Only files that are part of the build (have a compiled .olean): stray templates and
        # standalone scripts in the folder are not part of the claim.
        built = local / ".lake/build/lib/lean"
        files = [str(f.relative_to(local)) for f in local.rglob("*.lean")
                 if ".lake" not in f.parts and f.name not in ("lakefile.lean", AUDIT_FILE)
                 and (built / f.relative_to(local)).with_suffix(".olean").exists()]
        for h in standards.forbidden_lean(local, files):
            # std models in External/ are axioms by design: allowed when listed in [trust].models
            if h["construct"] == "axiom":
                line = (local / h["file"]).read_text(errors="replace").splitlines()[h["line"] - 1]
                mm = re.search(r"axiom\s+([^\s:({\[]+)", line)
                if mm and (mm.group(1) in listed or mm.group(1).split(".")[-1] in listed):
                    continue
            if h["construct"] == "sorry" and Path(h["file"]).parts[:2] == tuple(Path(extracted_rel(m)).parts[:2]):
                h["construct"] = "sorry (generated: item Aeneas could not translate)"
            hits.append(dict(h, variant=name) if len(locals_) > 1 else h)
    return hits[:500]


def load_overrides(proj):
    of = proj / "functions.toml"
    return {e["id"]: e for e in tomllib.loads(of.read_text()).get("function", [])} if of.exists() else {}


def load_json(p, default=None):
    try:
        return json.loads(Path(p).read_text())
    except (OSError, ValueError):
        return default


def history(lib, limit=20):
    d = results_dir(lib)
    out = []
    for f in sorted(d.glob("20*.json"), reverse=True)[:limit + 1]:
        h = load_json(f)
        if h:
            out.append(h)
    return out


def soundness_hits(res):
    """Known soundness bugs (toolchain/soundness.toml) in a tool version this run used."""
    f = ROOT / "toolchain/soundness.toml"
    bugs = tomllib.loads(f.read_text()).get("bug", []) if f.exists() else []
    tc = res.get("toolchain", {})
    return [b for b in bugs if str(tc.get(b.get("tool"), "")) in [str(v) for v in b.get("versions", [])]]


def evaluate(lib, m, res, proj, write_card=False):
    """Labels, the ten gates, entry status and CLAIM.md, from a finished result."""
    overrides = load_overrides(proj)
    for f in (res.get("functions") or {}).get("functions", []):
        ov = overrides.get(f["id"]) or overrides.get(f["id"].split("@L")[0], {})
        f["label"] = standards.function_label(f, m["tool"], ov)
        if ov.get("label"):
            f["declared_label"] = ov["label"]
    d = results_dir(lib)
    hist = [h for h in history(lib) if h.get("finished") != res.get("finished")]
    mutants = load_json(d / "mutants.json")
    upstream = load_json(d / "upstream.json")
    g, label = standards.gates(m, res, overrides, hist, mutants, versions().get("container", {}))
    hits = soundness_hits(res)
    status = standards.entry_status(m, res, g, admitted(lib), hist, hits)
    res["admission"] = {"status": status, "label": label, "gates": g, "passed": sum(x["pass"] for x in g.values()),
                        "soundness_bugs": hits, "admitted": admitted(lib)}
    if write_card:
        card = standards.claim_card(m, res, g, label, status, res.get("archive_sha256"), upstream)
        if hits:
            card = card.replace("\n## Code", "\n**Known soundness bug in a tool used:** "
                                + "; ".join(b.get("note", b.get("tool", "")) for b in hits) + "\n\n## Code", 1)
        (entry_dir(lib, m) / "CLAIM.md").write_text(card)
    return res["admission"]


def write_result(lib, res):
    d = results_dir(lib)
    if res.get("partial"):
        d = d / "partial"  # `run --functions` results never replace latest.json
    d.mkdir(parents=True, exist_ok=True)
    stamp = res["finished"].replace(":", "")
    (d / f"{stamp}.json").write_text(json.dumps(res, indent=1))
    (d / "latest.json").write_text(json.dumps(res, indent=1))
    report()
    p = res.get("prove", {})
    a = res.get("admission", {})
    log(f"{lib}: {p.get('proved', 0)}/{p.get('total', 0)} proved; entry {a.get('status')} "
        f"({a.get('passed', 0)}/10 gates, strength {a.get('label')}) -> {d.relative_to(ROOT)}/latest.json")


def latest_results():
    """One latest.json per entry: results/<lib>/ (old) and results/<name>/<version>/ (new)."""
    fs = sorted((ROOT / "results").glob("*/latest.json")) + sorted((ROOT / "results").glob("*/*/latest.json"))
    best = {}
    for f in fs:
        r = load_json(f, {})
        if not r:
            continue
        k = (r.get("library", "").split("/")[0], r.get("version") or r.get("commit"))
        if k not in best or load_json(best[k], {}).get("finished", "") < r.get("finished", ""):
            best[k] = f
    return sorted(best.values())


def report():
    rows = []
    for f in latest_results():
        r = json.loads(f.read_text())
        p = r.get("prove", {})
        ex = r.get("extract", {})
        fi = r.get("functions", {})
        proofs_clean = p.get("ok") and p.get("total") and not p.get("sorries")
        # "complete" needs every function verified or fixed (Yerin's rule), not just clean proofs.
        status = ("extract failed" if ex and not ex.get("ok") else "extracted" if ex and not p else
                  "complete" if proofs_clean and fi.get("complete") else
                  f"open: {fi.get('open', '?')} functions" if fi else "in progress")
        adm = r.get("admission") or {}
        rows.append(f"| {r.get('entry', r['library'])} | {r['tool']} | {r.get('version') or r['commit'][:10]} | "
                    f"{p.get('proved', 0)}/{p.get('total', 0)} | {p.get('sorries', '-')} | {p.get('axiom_thms', '-')} | "
                    f"{len(ex.get('assumed_axioms', [])) if ex else '-'} | {len(ex.get('unsupported', [])) if ex else '-'} | "
                    f"{fi.get('verified', 0) + fi.get('fixed', 0) if fi else '-'}/{fi.get('total', '-') if fi else '-'} | "
                    f"{status} | {adm.get('label', '-')} | {adm.get('status', '-')} ({adm.get('passed', 0)}/10) | {r['finished']} |")
    tables = []
    for f in latest_results():
        r = json.loads(f.read_text())
        fi = r.get("functions", {})
        opn = [x for x in fi.get("functions", []) if x["status"] == "open"]
        if opn:
            tables.append(f"\n## {r['library']}: open functions ({len(opn)} of {fi['total']})\n\n| Function | Why open |\n|---|---|\n"
                          + "\n".join(f"| `{x['id']}` | {x.get('why', '')} |" for x in opn) + "\n")
        pf = r.get("prove", {}).get("per_function")
        if pf:
            tables.append(f"\n## {r['library']}: proved goals per function\n\n| Function | Proved | Total | Status |\n|---|---|---|---|\n"
                          + "\n".join(f"| {k} | {e['proved']} | {e['total']} | {'done' if e['proved'] == e['total'] else 'open'} |"
                                      for k, e in sorted(pf.items(), key=lambda kv: (kv[1]['proved'] == kv[1]['total'], kv[0]))) + "\n")
    (ROOT / "results/SUMMARY.md").write_text(
        "# Verification results\n\nGenerated by `vpipe report`. One row per library, latest run.\n\n"
        "Extra-axiom thms = hand-written theorems whose `#print axioms` goes beyond propext/Classical.choice/Quot.sound (not counted as proved; unaudited ones are also not counted).\n"
        "Axioms = std functions modelled by an unproven axiom; Skipped = items Aeneas could not translate.\n\n"
        "Functions = functions in the pinned source that are verified or have a verified fix, out of all of them. "
        "A library is complete only when this is N/N.\n\n"
        "Strength = weakest per-function label (full-correctness > safety-contracts > no-ub > bounded > tested; "
        "unlabelled = functions.toml gives no label). Entry = status under the admission standard and gates passed; "
        "only libs/ entries can be verified, see each CLAIM.md.\n\n"
        "| Library | Tool | Version | Proved | Sorries | Extra-axiom thms | Axioms | Skipped | Functions | Progress | Strength | Entry | Run |\n|---|---|---|---|---|---|---|---|---|---|---|---|---|\n"
        + "\n".join(rows) + "\n" + "".join(tables))


# ---------------------------------------------------------------- new library
def new(lib, lang, upstream, commit, version, module=None):
    """New entries start in candidates/<name>/<version>/ with vpipe.toml, proof/, spec/ and pipeline/run.sh."""
    tool = "lean-aeneas" if lang == "rust" else "framac"
    if not version:
        raise SystemExit("--version is required (entries live in candidates/<name>/<version>/)")
    entry = ROOT / "candidates" / lib / version
    proj = entry / "proof"
    p = entry / "vpipe.toml"
    if entry.exists() or (ROOT / "libs" / lib / version).exists():
        raise SystemExit(f"{lib} {version} already exists")
    proj.mkdir(parents=True)
    mod = module or "".join(w.title() for w in re.split(r"[-_]", lib))
    t = (ROOT / "templates" / tool / "manifest.toml").read_text()
    p.write_text(t.format(name=lib, lang=lang, tool=tool, upstream=upstream, commit=commit,
                          version=version, module=mod, date=now()[:10]))
    tdir = ROOT / "templates" / tool / "project"
    for f in tdir.rglob("*"):
        if f.is_file():
            rel = Path(str(f.relative_to(tdir)).replace("MODULE", mod))
            (proj / rel).parent.mkdir(parents=True, exist_ok=True)
            txt = f.read_text().replace("{{module}}", mod).replace("{{lib}}", lib)
            if not f.name.endswith(".tmpl"):  # .tmpl files are rendered on every run instead
                txt = txt.replace("{{aeneas_commit}}", versions()["aeneas"]["commit"])
            txt = txt.replace("{{lean_version}}", versions()["lean"]["version"])
            (proj / rel).write_text(txt)
    write_entry_extras(entry, tomllib.loads(p.read_text()))
    log(f"created {entry}; write [scope] in vpipe.toml and get it reviewed, then `vpipe run {lib}/{version}`")


def write_entry_extras(entry, m):
    """spec/README.md (the plain-words spec, from [scope]) and pipeline/run.sh (how to re-check)."""
    (entry / "spec").mkdir(exist_ok=True)
    sc = m.get("scope", {})
    spec = entry / "spec/README.md"
    if not spec.exists():
        spec.write_text(f"# {m['name']} {m.get('version', '')}: specification\n\n"
                        f"{sc.get('summary', 'Write what the library promises, in plain words, before any proof work.')}\n\n"
                        "## Properties (success criteria, from vpipe.toml [scope].properties)\n\n"
                        + "".join(f"- {x}\n" for x in sc.get("properties", []))
                        + "\n## Formal spec files (in proof/)\n\n" + "".join(f"- {x}\n" for x in sc.get("spec_files", [])))
    (entry / "pipeline").mkdir(exist_ok=True)
    depth = len(entry.relative_to(ROOT).parts) + 1
    (entry / "pipeline/run.sh").write_text(
        "#!/usr/bin/env bash\n# Re-check this entry from clean with the pinned toolchain (generated by vpipe).\n"
        "set -euo pipefail\n"
        f'cd "$(dirname "$0")/{"/".join([".."] * depth)}"\n'
        f'exec python3 bin/vpipe.py run {m["name"]}/{m.get("version", "")} --clean "$@"\n')


def export_entry(lib, dest=None):
    """With --dest <repo>: copy the entry into <repo>/candidates/<name>/<version>/ in the verified-libs
    layout (CLAIM.md, vpipe.toml, functions.toml in proof/, spec/, proof/, pipeline/run.sh), leaving
    the working folder alone. Admitted entries go to libs/ instead.
    Without --dest: move an older libraries/<lib>/ folder into candidates/<name>/<version>/ here,
    move its results, and leave a symlink at the old path so sessions working there keep working."""
    if dest:
        m = manifest(lib)
        d, proj = entry_dir(lib, m), proof_dir(lib, m)
        ver = m.get("version") or m["commit"][:12]
        area = "libs" if admitted(lib) else "candidates"
        out = Path(dest).resolve() / area / m["name"] / ver
        if out.exists():
            shutil.rmtree(out)
        ign = shutil.ignore_patterns(".lake", "target", "__pycache__", "CLAIM.md", "vpipe.toml", "mutants.toml",
                                     "mutants.suggested.toml", "spec", "pipeline")
        shutil.copytree(proj, out / "proof", ignore=ign)
        for f in ("vpipe.toml", "CLAIM.md", "mutants.toml"):
            if (d / f).exists():
                shutil.copy(d / f, out / f)
        if (d / "spec").is_dir():
            shutil.copytree(d / "spec", out / "spec")
        write_entry_extras(out, m)
        if not (out / "CLAIM.md").exists():
            log("no CLAIM.md yet: run the entry (or `vpipe card`) first")
        log(f"exported {lib} -> {out}")
        return out
    old = ROOT / "libraries" / lib
    if old.is_symlink() or not (old / "vpipe.toml").exists():
        raise SystemExit(f"{old} is not an older-layout library folder")
    m = tomllib.loads((old / "vpipe.toml").read_text())
    ver = m.get("version") or m["commit"][:12]
    entry = ROOT / "candidates" / m["name"] / ver
    if entry.exists():
        raise SystemExit(f"{entry} already exists")
    (entry / "proof").mkdir(parents=True)
    for f in old.iterdir():
        dst = entry / f.name if f.name in ("vpipe.toml", "mutants.toml", "CLAIM.md") else entry / "proof" / f.name
        shutil.move(str(f), str(dst))
    old.rmdir()
    old.symlink_to(Path("..") / "candidates" / m["name"] / ver / "proof", target_is_directory=True)
    write_entry_extras(entry, m)
    rold, rnew = ROOT / "results" / lib, ROOT / "results" / m["name"] / ver
    if rold.exists() and not rnew.exists():
        rnew.mkdir(parents=True)
        for f in rold.iterdir():
            shutil.move(str(f), str(rnew / f.name))
        rold.rmdir() if not any(rold.iterdir()) else None
    log(f"moved {old} -> {entry} (old path is now a symlink to proof/)")
    return entry


def card(lib):
    """Re-evaluate the gates and rewrite CLAIM.md from the latest result (after editing functions.toml,
    [scope], [trust] or [review], or after `vpipe mutate` / `check-upstream`)."""
    m = manifest(lib)
    f = results_dir(lib) / "latest.json"
    res = load_json(f)
    if not res:
        raise SystemExit(f"no result for {lib}; run `vpipe run {lib}` first")
    a = evaluate(lib, m, res, proof_dir(lib, m), write_card=True)
    f.write_text(json.dumps(res, indent=1))
    report()
    return a


def admit(lib):
    """candidates/<name>/<version>/ -> libs/<name>/<version>/, only when every gate passes."""
    m = manifest(lib)
    d = locate(lib)
    if not d or d.parent.parent != ROOT / "candidates":
        raise SystemExit(f"{lib} is not a candidates/ entry")
    a = card(lib)
    failing = [k for k, v in a["gates"].items() if not v["pass"]]
    if failing or a.get("soundness_bugs"):
        raise SystemExit(f"not admitted: gates failing: {failing}" + (" ; known tool soundness bug" if a.get("soundness_bugs") else ""))
    dst = ROOT / "libs" / d.parent.name / d.name
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.move(str(d), str(dst))
    a = card(f"{d.parent.name}/{d.name}")
    log(f"admitted {lib}: {dst.relative_to(ROOT)} status {a['status']}")
    return a


# ---------------------------------------------------------------- upstream releases (stale marking)
VERSION_TAG_RE = r"^(?:refs/tags/)?(?:v|{name}[-_]v?)?(\d+(?:\.\d+){{1,3}})$"


def check_upstream(lib, scaffold=False):
    """List upstream release tags. A release newer than the pinned version is recorded as stale
    (not verified); the pinned entry keeps its status. --scaffold copies the entry to
    candidates/<name>/<new version>/ with the new commit, to be re-proved."""
    m = manifest(lib)
    r = sh(["git", "ls-remote", "--tags", m["upstream"]], check=False, capture=True, timeout=300)
    pat = re.compile(m.get("release_tags", VERSION_TAG_RE.format(name=re.escape(m["name"]))))
    tags = {}
    for line in r.stdout.splitlines():
        sha, ref = (line.split("\t") + [""])[:2]
        peeled = ref.endswith("^{}")
        mt = pat.match(ref[:-3] if peeled else ref)
        if mt:
            v = mt.group(1)
            if peeled or v not in tags:
                tags[v] = sha  # an annotated tag's ^{} line is the commit itself
    key = lambda v: tuple(int(x) for x in v.split("."))
    cur = m.get("version", "")
    latest = max(tags, key=key) if tags else None
    newer = bool(latest and cur and re.fullmatch(r"\d+(\.\d+)*", cur) and key(latest) > key(cur))
    out = {"checked": now(), "pinned": cur, "latest": latest, "latest_commit": tags.get(latest), "newer": newer,
           "newer_releases": sorted([v for v in tags if cur and re.fullmatch(r"\d+(\.\d+)*", cur) and key(v) > key(cur)], key=key),
           "ok": r.returncode == 0}
    d = results_dir(lib)
    d.mkdir(parents=True, exist_ok=True)
    (d / "upstream.json").write_text(json.dumps(out, indent=1))
    if newer and scaffold and locate(lib):
        src_entry = locate(lib)
        dst = ROOT / "candidates" / m["name"] / latest
        if not dst.exists():
            shutil.copytree(src_entry, dst, symlinks=True, ignore=shutil.ignore_patterns(".lake", "CLAIM.md"))
            t = (dst / "vpipe.toml").read_text()
            t = re.sub(r'(?m)^commit\s*=.*$', f'commit = "{tags[latest]}"   # {latest}, scaffolded by check-upstream', t)
            t = re.sub(r'(?m)^version\s*=.*$', f'version = "{latest}"', t)
            t = re.sub(r'(?m)^archive_sha256\s*=.*\n', "", t)
            (dst / "vpipe.toml").write_text(t)
            out["scaffolded"] = str(dst.relative_to(ROOT))
            (d / "upstream.json").write_text(json.dumps(out, indent=1))
    if load_json(d / "latest.json"):
        card(lib)
    return out


# ---------------------------------------------------------------- planted bugs (gate 6)
# <entry>/mutants.toml is written by the adversarial reviewer (standard: at least 10, chosen by the
# reviewer, never by the proof author):
#   chosen_by = "adversarial review, <session link>, 2026-10-24"
#   [[mutant]]
#   file = "src/baseline.rs"     # relative to the source tree the tool reads (after patches)
#   find = "crc >> 1"            # must occur exactly once in that file
#   replace = "crc >> 2"
#   note = "wrong shift in the bitwise loop"
# `vpipe mutate <lib>` applies each one alone, re-runs extraction and proofs, and records whether
# the proofs rejected it. `--suggest N` writes mutants.suggested.toml for the reviewer to pick from.

def apply_mutant(tree, mu):
    f = tree / mu["file"]
    text = f.read_text()
    n = text.count(mu["find"])
    if n != 1:
        raise ValueError(f"{mu['file']}: `{mu['find']}` occurs {n} times (must be exactly once)")
    f.write_text(text.replace(mu["find"], mu["replace"], 1))


MUTATION_OPS = [(" + ", " - "), (" - ", " + "), (" < ", " <= "), (" <= ", " < "), (" > ", " >= "), (" >= ", " > "),
                (" == ", " != "), (" != ", " == "), (" & ", " | "), (" | ", " & "), (" ^ ", " & "), (">> 1", ">> 2"),
                ("<< 1", "<< 2"), (" && ", " || "), (" || ", " && "), ("wrapping_add", "wrapping_sub")]


def suggest_mutants(m, tree, res, n):
    """Candidate planted bugs inside verified functions, one operator change each, spread over
    functions (round robin) so the reviewer sees every function's logic tested."""
    per_fn = []
    fns = [f for f in (res.get("functions") or {}).get("functions", []) if f["status"] != "open"]
    for fn in fns:
        f = tree / fn["file"]
        if not f.exists():
            continue
        lines = f.read_text().splitlines()
        text = "\n".join(lines)
        cands, seen = [], set()
        for i in range(fn["line"], min(len(lines), fn["line"] + 80)):
            line = lines[i]
            st = line.strip()
            if re.match(r"(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:unsafe\s+)?fn\s", st):
                break  # next function
            if st.startswith(("//", "/*", "*", "#", "use ")):
                continue
            for a, b in MUTATION_OPS:
                if a in line:
                    find, repl = st, line.replace(a, b, 1).strip()
                    if find == repl or text.count(find) != 1 or find in seen:
                        continue
                    seen.add(find)
                    cands.append({"file": fn["file"], "find": find, "replace": repl,
                                  "note": f"{fn['id']}: `{a.strip()}` -> `{b.strip()}`"})
                    break
        if cands:
            per_fn.append(cands)
    out = []
    while per_fn and len(out) < n:
        for c in list(per_fn):
            if c:
                out.append(c.pop(0))
            if not c:
                per_fn.remove(c)
            if len(out) >= n:
                break
    return out


def toml_str(x):
    return json.dumps(x)  # TOML basic strings use the same escapes as JSON for these characters


def mutate(lib, suggest=0, only=None):
    m = manifest(lib)
    tool = m["tool"]
    if variants(m):
        raise SystemExit("mutate does not support [[variant]] entries yet")
    setup("lean" if tool == "lean-aeneas" else "framac")
    entry, proj = entry_dir(lib, m), proof_dir(lib, m)
    src = fetch(m)
    tree, info = prepare_source(m, src, proj, run_tests=False)
    if info.get("error"):
        raise SystemExit(info["error"])
    base = load_json(results_dir(lib) / "latest.json", {})
    if suggest:
        ms = suggest_mutants(m, tree, base, suggest)
        body = "# Suggested planted bugs (vpipe mutate --suggest). The reviewer picks at least 10, may write\n" \
               "# others, and copies them into mutants.toml with chosen_by set.\n\n"
        for mu in ms:
            body += "[[mutant]]\n" + "".join(f"{k} = {toml_str(v)}\n" for k, v in mu.items()) + "\n"
        (entry / "mutants.suggested.toml").write_text(body)
        log(f"wrote {len(ms)} suggestions to {entry / 'mutants.suggested.toml'}")
        return {"suggested": len(ms)}
    mf = entry / "mutants.toml"
    if not mf.exists():
        raise SystemExit(f"{mf} missing (the reviewer writes it; `--suggest 20` gives candidates)")
    spec = tomllib.loads(mf.read_text())
    proved0 = {t["name"] for t in (base.get("prove") or {}).get("theorems", []) if t.get("status") == "proved"}
    if not proved0 and tool == "lean-aeneas":
        raise SystemExit("no proved theorems in the latest run; run the entry first")
    goals0 = (base.get("prove") or {}).get("proved", 0)
    results = []
    for i, mu in enumerate(spec.get("mutant", [])):
        if only is not None and i not in only:
            continue
        mt = WORK / m["name"] / "mutant-tree"
        shutil.rmtree(mt, ignore_errors=True)
        shutil.copytree(tree, mt, ignore=shutil.ignore_patterns(".git", "target"))
        rec = {"i": i, **mu}
        try:
            if tool == "lean-aeneas":
                apply_mutant(mt / m.get("extract", {}).get("crate_dir", "."), mu) if not (mt / mu["file"]).exists() \
                    else apply_mutant(mt, mu)
                local = WORK / m["name"] / "mutant-proj"
                mirror(proj, local, delete=True)
                shutil.rmtree(local / ".lake/build", ignore_errors=True)
                ex = extract_rust(m, mt, local)
                if not (local / extracted_rel(m) / "Funs.lean").exists():
                    rec.update(outcome="invalid", why="does not extract")
                else:
                    pr = prove_lean(m, local)
                    still = {t["name"] for t in pr["theorems"] if t.get("status") == "proved"}
                    lost = sorted(proved0 - still)
                    rec.update(outcome="caught" if lost or not pr["ok"] else "survived", broken_theorems=lost[:20],
                               extract_ok=ex["ok"])
            else:
                pr = prove_framac(m, tree, proj, mutant=mu, tag="mutant")
                rec.update(outcome="caught" if pr["proved"] < goals0 or not pr["ok"] else "survived",
                           proved=f"{pr['proved']}/{pr['total']}")
        except ValueError as e:
            rec.update(outcome="invalid", why=str(e))
        log(f"mutant {i}: {rec['outcome']} ({mu.get('note', '')})")
        results.append(rec)
    out = {"commit": m["commit"], "chosen_by": spec.get("chosen_by"), "file_sha256": hashlib.sha256(mf.read_bytes()).hexdigest(),
           "total": sum(r["outcome"] != "invalid" for r in results), "caught": sum(r["outcome"] == "caught" for r in results),
           "invalid": sum(r["outcome"] == "invalid" for r in results), "finished": now(), "mutants": results}
    if only is None:
        (results_dir(lib) / "mutants.json").write_text(json.dumps(out, indent=1))
        if base:
            card(lib)
    return out


# ---------------------------------------------------------------- self-test
def check_fixture(kind, full=False):
    """Run one fixture through the real extract/prove code. Prints/returns proved/total."""
    if kind == "framac":
        setup("framac")
        m = {"name": "selftest-c", "framac": {"files": ["sat.c"]}}
        r = prove_framac(m, ROOT / "selftest/c-demo", WORK / "selftest-c-none")
        return {"ok": r["ok"], "proved": r["proved"], "total": r["total"]}
    setup("lean")
    proj = WORK / "selftest-rust" / "proj"
    shutil.rmtree(proj, ignore_errors=True)
    shutil.copytree(ROOT / "selftest/rust-demo/lean", proj)
    m = {"name": "selftest-rust", "extract": {"module": "Demo"}}
    e = extract_rust(m, ROOT / "selftest/rust-demo", proj)
    out = {"ok": e["ok"], "extracted": sorted(p.name for p in (proj / extracted_rel(m)).glob("*.lean"))}
    if e["ok"] and full:
        p = prove_lean(m, proj)
        out.update(ok=p["ok"] and p["sorries"] == 0, proved=p["proved"], total=p["total"],
                   sorries=p["sorries"], errors=p["errors"][:5])
    return out


def standards_selftest():
    """The admission checks must catch shortcuts and must never call a candidate verified."""
    fails = []
    t = WORK / "selftest-standards"
    shutil.rmtree(t, ignore_errors=True)
    t.mkdir(parents=True)
    (t / "P.lean").write_text("-- sorry in a comment is fine\n/- native_decide here too -/\n"
                              "theorem a : 1 = 1 := by native_decide\ntheorem b : True := sorry\naxiom cheat : False\n")
    hits = sorted(h["construct"] for h in standards.forbidden_lean(t, ["P.lean"]))
    if hits != ["axiom", "native_decide", "sorry"]:
        fails.append(f"forbidden_lean: {hits}")
    (t / "c.c").write_text("/*@ admit lemma x: \\true; */\nint f(void) { return 0; }\n")
    ch = sorted(h["construct"] for h in standards.forbidden_framac(t, ["c.c"], ["-wp-literals"]))
    if ch != ["WP run without -wp-rte", "admit clause"]:
        fails.append(f"forbidden_framac: {ch}")
    m = {"name": "x", "version": "1.0.0", "upstream": "u", "commit": "c" * 40, "tool": "lean-aeneas"}
    res = {"commit": m["commit"], "prove": {"ok": True, "proved": 1, "total": 1, "theorems": [{"name": "t", "status": "proved"}],
                                            "replay": {"ok": True}},
           "functions": {"total": 1, "verified": 1, "fixed": 0, "open": 0, "complete": True,
                         "functions": [{"id": "src/lib.rs:f", "status": "verified", "label": "full-correctness"}]}}
    g, label = standards.gates(m, res, {}, [], None)
    if all(x["pass"] for x in g.values()) or label != "full-correctness":
        fails.append("gates passed an entry with no pinned archive, reviews or planted bugs")
    if standards.entry_status(m, res, {k: {"pass": True} for k in g}, False, [], []) != "candidate":
        fails.append("a candidate was reported verified")
    if standards.function_label({"status": "verified"}, "lean-aeneas", {"label": "full-correctness", "verified_by": "cbmc"}) != "bounded":
        fails.append("CBMC evidence was not capped at bounded")
    card_ = standards.claim_card(m, res, g, label, "candidate", "ab" * 32, None)
    if not card_.startswith("---\nlibrary: x\n") or "status: candidate" not in card_:
        fails.append("claim card front matter")
    shutil.rmtree(t, ignore_errors=True)
    return fails


def selftest(full=False):
    """Parsers, manifests, and both fixtures. With --full also builds and proves the Lean fixture
    (needs mathlib, so only practical once the mathlib cache exists)."""
    fails = []
    sample = "warning: A/Proofs.lean:12:8: declaration uses `sorry`\nerror: A/B.lean:3:1: omega failed\n"
    if SORRY_RE.findall(sample) != [("A/Proofs.lean", "12")]:
        fails.append("sorry parser")
    if [(f or f2, l or l2) for f, l, f2, l2 in ERR_RE.findall(sample)] != [("A/B.lean", "3")]:
        fails.append("error parser")
    for lib in all_libraries():
        try:
            manifest(lib)
        except SystemExit as e:
            fails.append(f"manifest {lib}: {e}")
    # Function scanners on the fixtures: every function must be found.
    rs = [f["id"] for f in scan_rust_functions(ROOT / "selftest/rust-demo")]
    if rs != ["src/lib.rs:add_sat"]:
        fails.append(f"rust function scan: {rs}")
    cs = [f["id"] for f in scan_c_functions(ROOT / "selftest/c-demo", ["sat.c"])]
    if cs != ["sat.c:add_sat", "sat.c:count_nonzero"]:
        fails.append(f"c function scan: {cs}")
    fails += standards_selftest()
    for kind in ("framac", "rust"):
        try:
            r = check_fixture(kind, full)
            if not r["ok"]:
                fails.append(f"{kind} fixture: {r}")
        except BaseException as e:
            fails.append(f"{kind} fixture: {e}")
    print(json.dumps({"ok": not fails, "failures": fails, "full": full}))
    return not fails


# ---------------------------------------------------------------- self-update
def snapshot(tag):
    d = ROOT / "self/snapshots"
    d.mkdir(parents=True, exist_ok=True)
    out = d / f"{now().replace(':', '')}-{tag}.tar.gz"
    with tarfile.open(out, "w:gz") as t:
        for p in SELF_EDITABLE:
            if (ROOT / p).exists():
                t.add(ROOT / p, arcname=p)
    return out


def rollback(snap=None):
    snaps = sorted((ROOT / "self/snapshots").glob("*.tar.gz"))
    s = Path(snap) if snap else snaps[-1]
    for p in SELF_EDITABLE:
        if p != "self/CHANGELOG.md" and (ROOT / p).is_dir():
            shutil.rmtree(ROOT / p)
    keep = (ROOT / "self/CHANGELOG.md").read_text() if (ROOT / "self/CHANGELOG.md").exists() else ""
    with tarfile.open(s) as t:
        t.extractall(ROOT, filter="data")
    (ROOT / "self/CHANGELOG.md").write_text(keep)  # the log survives rollbacks
    log(f"rolled back to {s.name}")


def tree_hash(paths):
    h = {}
    for p in paths:
        base = ROOT / p if not str(p).startswith("/") else Path(p)
        files = [base] if base.is_file() else sorted(base.rglob("*")) if base.exists() else []
        for f in files:
            if f.is_file() and "snapshots" not in f.parts and "__pycache__" not in f.parts:
                h[str(f)] = hashlib.sha256(f.read_bytes()).hexdigest()
    return h


def gate(full=False):
    """Protected acceptance check, run in a fresh interpreter so it exercises the new code."""
    args = [sys.executable, str(ROOT / "self/gate.py")] + (["--full"] if full else [])
    return sh(args, check=False).returncode == 0


def changelog(entry):
    f = ROOT / "self/CHANGELOG.md"
    f.write_text(f.read_text() + "\n" + entry.strip() + "\n")


def bump_version():
    v = (ROOT / "VERSION").read_text().strip().split(".")
    v[-1] = str(int(v[-1]) + 1)
    (ROOT / "VERSION").write_text(".".join(v) + "\n")
    return ".".join(v)


class Lock:
    """mkdir-based lock so two sessions never self-update at once."""
    def __init__(self, name):
        self.p = ROOT / "self" / f".{name}.lock"

    def __enter__(self):
        try:
            self.p.mkdir()
        except FileExistsError:
            raise SystemExit(f"{self.p} held by another session (remove it if stale)")
        (self.p / "owner").write_text(f"{os.uname().nodename} {now()}")

    def __exit__(self, *a):
        shutil.rmtree(self.p, ignore_errors=True)


def improve(goal=None, propose=False, budget=80, branch=False):
    with Lock("improve"):
        guard = SELF_FORBIDDEN + [str(NOTES)]
        before_guard = tree_hash(guard)
        before = tree_hash(SELF_EDITABLE)
        snap = snapshot("pre-improve")
        prompt = (ROOT / "templates/prompts/improve.md").read_text()
        prompt = prompt.replace("{{goal}}", goal or "(none given: pick the highest-value item)")
        prompt = prompt.replace("{{mode}}", "PROPOSE ONLY: write self/proposals/<timestamp>.md, change nothing else"
                                if propose else "APPLY")
        prompt = prompt.replace("{{now}}", now()).replace("{{root}}", str(ROOT)).replace("{{notes}}", str(NOTES))
        prompt = prompt.replace("{{editable}}", ", ".join(SELF_EDITABLE))
        tools = ("Read Edit Write Glob Grep Bash(ls:*) Bash(cat:*) Bash(grep:*) Bash(head:*) "
                 "Bash(tail:*) Bash(python3:*) Bash(bash -n:*) Bash(lake:*) Bash(lean:*) Bash(frama-c:*)")
        sh(["claude", "-p", prompt, "--max-turns", str(budget), "--permission-mode", "acceptEdits",
            "--allowedTools", tools, "--add-dir", str(NOTES)], cwd=ROOT, check=False, timeout=3 * 3600)
        if tree_hash(guard) != before_guard:
            # Another session may have legitimately written notes/results meanwhile; only fail on
            # paths the agent could plausibly have touched (proofs/, libraries/).
            changed = [k for k, v in tree_hash(guard).items() if before_guard.get(k) != v]
            bad = [c for c in changed if "/proofs/" in c or "/libraries/" in c]
            if bad:
                rollback(snap)
                changelog(f"## {now()} improve REJECTED\n- touched protected paths: {bad[:5]}\n- rolled back to {snap.name}")
                return False
        changed = sorted(k.replace(str(ROOT) + "/", "") for k, v in tree_hash(SELF_EDITABLE).items()
                         if before.get(k) != v)
        code_changed = [c for c in changed if c not in ("self/CHANGELOG.md",)]
        if propose or not code_changed:
            log("no code changes" if not propose else "proposal written")
            return True
        # Full gate (Lean fixture built and proved) whenever mathlib can be restored quickly, so
        # Lean-side changes are exercised, not just parsed. The axiom-audit change showed why.
        full = (VH / "lake" / mathlib_cache_key() / ".lake/packages/mathlib").exists() or any(
            any(d.glob("*mathlib*.tar*")) or any(d.glob("lake-packages-*.tar*")) for d in cache_dirs() if d.exists())
        ok = gate(full=full)
        if not ok:
            rollback(snap)
            changelog(f"## {now()} improve ROLLED BACK\n- selftest failed after changing: {code_changed}\n"
                      f"- restored {snap.name}")
            return False
        ver = bump_version()
        changelog(f"- kept: selftest passed; pipeline version {ver}; files: {code_changed}")
        if branch:
            commit_branch(f"vpipe improve: {goal or 'self-update'} (v{ver})", code_changed + ["VERSION", "self/CHANGELOG.md"])
        return True


def commit_branch(msg, files):
    """In a git clone (verified-libs), put a kept self-change on its own branch `vpipe/improve-<ts>`
    for a PR, then return to the starting branch. Never pushes: pushing and the PR are a separate,
    approved step (CI or a person). Results-only changes never get here."""
    if not (ROOT / ".git").exists():
        log("not a git clone; change left in place")
        return None
    name = "vpipe/improve-" + now().replace(":", "").replace("-", "")
    start = sh(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=ROOT, capture=True).stdout.strip()
    sh(["git", "switch", "-c", name], cwd=ROOT)
    sh(["git", "add", "--", *files], cwd=ROOT)
    sh(["git", "commit", "-q", "-m", msg], cwd=ROOT)
    sh(["git", "switch", "-q", start], cwd=ROOT)
    log(f"committed to branch {name}; open a PR from it")
    return name


def upgrade_tools():
    """Self-update the toolchain pin: try the newest Aeneas nightly, keep it only if selftest passes."""
    with Lock("improve"):
        v = versions()
        tags = sh("git ls-remote --tags https://github.com/AeneasVerif/aeneas 'nightly-*'",
                  capture=True).stdout.split()
        tags = sorted(t.split("refs/tags/")[1] for t in tags if "refs/tags/" in t)
        if not tags or tags[-1] == v["aeneas"]["tag"]:
            log("Aeneas pin is current")
            return True
        new_tag = tags[-1]
        snap = snapshot("pre-upgrade")
        tmp = WORK / "upgrade"
        shutil.rmtree(tmp, ignore_errors=True)
        tmp.mkdir(parents=True)
        sh(f"curl -fsSL '{v['aeneas']['url'].replace('{tag}', new_tag)}' | tar xz -C '{tmp}'")
        lean = (tmp / "backends/lean/lean-toolchain").read_text().strip().split(":v")[-1]
        commit = sh(f"git ls-remote https://github.com/AeneasVerif/aeneas refs/tags/{new_tag}",
                    capture=True).stdout.split()[0]
        vt = (ROOT / "toolchain/versions.toml").read_text()
        vt = vt.replace(v["aeneas"]["tag"], new_tag).replace(v["aeneas"]["commit"], commit)
        vt = re.sub(r'(\[lean\][^\[]*?version = ")[^"]+', rf"\g<1>{lean}", vt, flags=re.S)
        (ROOT / "toolchain/versions.toml").write_text(vt)
        if gate(full=True):
            ver = bump_version()
            changelog(f"## {now()} upgrade-tools\n- Aeneas {v['aeneas']['tag']} -> {new_tag} (Lean {lean}); "
                      f"full selftest passed; pipeline {ver}\n- why: stay current with upstream fixes; "
                      "library proofs must be re-run with `vpipe run-all` to see what broke")
            return True
        rollback(snap)
        changelog(f"## {now()} upgrade-tools ROLLED BACK\n- tried Aeneas {new_tag}; full selftest failed; kept {v['aeneas']['tag']}")
        return False


# ---------------------------------------------------------------- cli
def main():
    ap = argparse.ArgumentParser(prog="vpipe", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    s = ap.add_subparsers(dest="cmd", required=True)
    s.add_parser("setup").add_argument("which", nargs="?", default="all", choices=["lean", "framac", "all"])
    n = s.add_parser("new")
    n.add_argument("lib"); n.add_argument("--lang", required=True, choices=["rust", "c"])
    n.add_argument("--upstream", required=True); n.add_argument("--commit", required=True)
    n.add_argument("--version", default=""); n.add_argument("--module")
    for c in ("run", "run-all"):
        r = s.add_parser(c)
        if c == "run":
            r.add_argument("lib")
        r.add_argument("--agent", action="store_true", help="let a Claude agent write specs/proofs")
        r.add_argument("--rounds", type=int, default=3); r.add_argument("--budget", type=int, default=60)
        r.add_argument("--extract-only", action="store_true", help="Rust: stop after Aeneas (scope check)")
        r.add_argument("--improve", action="store_true", help="afterwards, run the self-update loop on what this run showed")
        r.add_argument("--functions", help="C: comma-separated functions to prove (quick check; result kept apart)")
        r.add_argument("--clean", action="store_true", help="rebuild every proof from scratch (no cached proof results); "
                       "two matching clean runs are admission gate 9")
    s.add_parser("report")
    s.add_parser("card", help="re-evaluate the admission gates and rewrite CLAIM.md").add_argument("lib")
    s.add_parser("admit", help="move a candidate that passes every gate into libs/").add_argument("lib")
    ex = s.add_parser("export", help="copy an entry into a verified-libs clone (--dest), or move libraries/<lib>/ into candidates/")
    ex.add_argument("lib"); ex.add_argument("--dest", help="root of a verified-libs clone")
    cu = s.add_parser("check-upstream", help="record newer upstream releases (stale marking)")
    cu.add_argument("lib", nargs="?"); cu.add_argument("--scaffold", action="store_true")
    nx = s.add_parser("next", help="open functions to work on next (callees verified first)")
    nx.add_argument("lib"); nx.add_argument("-n", type=int, default=20)
    tk = s.add_parser("take", help="record that you are working on a function (functions.toml claimed_by)")
    tk.add_argument("lib"); tk.add_argument("function"); tk.add_argument("--by", required=True)
    mu = s.add_parser("mutate", help="run the reviewer's planted bugs (mutants.toml) against the proofs")
    mu.add_argument("lib"); mu.add_argument("--suggest", type=int, default=0)
    mu.add_argument("--only", help="comma-separated mutant indexes (trial run; not recorded)")
    s.add_parser("selftest").add_argument("--full", action="store_true")
    i = s.add_parser("improve")
    i.add_argument("--goal"); i.add_argument("--propose", action="store_true")
    i.add_argument("--budget", type=int, default=80)
    i.add_argument("--branch", action="store_true", help="in a git clone, commit a kept change to its own branch for a PR")
    cf = s.add_parser("check-fixture"); cf.add_argument("kind", choices=["framac", "rust"])
    cf.add_argument("--full", action="store_true")
    s.add_parser("upgrade-tools")
    s.add_parser("rollback").add_argument("snapshot", nargs="?")
    a = ap.parse_args()
    if a.cmd == "setup":
        print(json.dumps(setup(a.which), indent=1))
    elif a.cmd == "new":
        new(a.lib, a.lang, a.upstream, a.commit, a.version, a.module)
    elif a.cmd == "run":
        r = run(a.lib, a.agent, a.rounds, a.budget, a.extract_only, a.clean,
                a.functions.split(",") if a.functions else None)
        if a.improve:
            improve(f"Learn from the run just finished: results/{a.lib}/latest.json")
        sys.exit(0 if (r.get("prove") or r.get("extract", {})).get("ok") else 1)
    elif a.cmd == "run-all":
        bad = [lib for lib in all_libraries()
               if not run(lib, a.agent, a.rounds, a.budget, a.extract_only, a.clean).get("prove", {}).get("ok")]
        if a.improve:
            improve("Learn from the run-all just finished: results/SUMMARY.md and each latest.json")
        sys.exit(1 if bad else 0)
    elif a.cmd == "report":
        report()
    elif a.cmd == "card":
        print(json.dumps(card(a.lib), indent=1))
    elif a.cmd == "admit":
        print(json.dumps(admit(a.lib), indent=1))
    elif a.cmd == "export":
        print(export_entry(a.lib, a.dest))
    elif a.cmd == "check-upstream":
        print(json.dumps({lib: check_upstream(lib, a.scaffold) for lib in ([a.lib] if a.lib else all_libraries())}, indent=1))
    elif a.cmd == "next":
        print(json.dumps(next_functions(a.lib, a.n), indent=1))
    elif a.cmd == "take":
        print(json.dumps(take(a.lib, a.function, a.by)))
    elif a.cmd == "mutate":
        r = mutate(a.lib, a.suggest, [int(x) for x in a.only.split(",")] if a.only else None)
        print(json.dumps({k: v for k, v in r.items() if k != "mutants"}, indent=1))
    elif a.cmd == "selftest":
        sys.exit(0 if selftest(a.full) else 1)
    elif a.cmd == "improve":
        sys.exit(0 if improve(a.goal, a.propose, a.budget, a.branch) else 1)
    elif a.cmd == "check-fixture":
        print(json.dumps(check_fixture(a.kind, a.full)))
    elif a.cmd == "upgrade-tools":
        sys.exit(0 if upgrade_tools() else 1)
    elif a.cmd == "rollback":
        rollback(a.snapshot)


if __name__ == "__main__":
    main()
