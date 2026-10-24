#!/usr/bin/env python3
"""vkit: install, check and use the verification toolkit.

  vkit doctor [--json]              what is installed, what is missing, which hosts are reachable
  vkit setup [lean|framac|cbmc|mathlib|all] [--yes]
                                    install pinned tools (shows the plan and asks first)
  vkit skills install [--agent claude|codex|gemini|DIR] [--yes] [--dry-run]
  vkit skills list
  vkit update                       git pull this checkout, then refresh installed skills
  vkit <anything else>              passed to the vpipe engine (new, run, run-all, report, selftest, ...)

Tool versions come from toolchain/versions.toml, the same pins the engine uses.
"""
import argparse, json, os, platform, shutil, socket, subprocess, sys, tarfile, time
from pathlib import Path

if sys.version_info < (3, 11):
    sys.exit("vkit needs Python 3.11 or newer (for tomllib).")
import tomllib

REPO = Path(__file__).resolve().parent.parent
PIPE = REPO  # the repo root is the engine root
SKILLS = REPO / "skills"
VH = Path(os.environ.get("VPIPE_HOME", Path.home() / ".vpipe"))
WORK = Path(os.environ.get("VPIPE_WORK", Path.home() / "vpipe-work"))
# User-level skill folders. Codex and Gemini CLI both read the shared Agent Skills folder
# ~/.agents/skills (Codex docs: developers.openai.com/codex/skills; Gemini CLI docs/cli/skills.md),
# so installing for both writes one copy. Inside a clone, .agents/skills -> skills/ serves both too.
AGENTS_HOME = Path(os.environ.get("GEMINI_CLI_HOME", Path.home()))
AGENT_SKILL_DIRS = {
    "claude": Path.home() / ".claude/skills",
    "codex": Path.home() / ".agents/skills",
    "gemini": AGENTS_HOME / ".agents/skills",
}
LEGACY_SKILL_DIRS = [Path(os.environ.get("CODEX_HOME", Path.home() / ".codex")) / "skills"]
HOSTS = {  # host -> what breaks without it
    "github.com": "Aeneas, Lean, CBMC release downloads and git clones",
    "static.rust-lang.org": "rustup toolchains",
    "release.lean-lang.org": "elan's normal Lean download (vkit falls back to GitHub)",
    "cache.mathlib.org": "prebuilt mathlib (without it mathlib compiles for hours)",
    "cache.nixos.org": "Frama-C via Nix",
    "opam.ocaml.org": "Frama-C via opam",
}


def log(*a):
    print("[vkit]", *a, file=sys.stderr, flush=True)


def env_path():
    e = dict(os.environ)
    e["PATH"] = os.pathsep.join([str(VH / "bin"), str(VH / "aeneas"), str(Path.home() / ".elan/bin"),
                                 str(Path.home() / ".cargo/bin"), str(Path.home() / ".nix-profile/bin"),
                                 "/nix/var/nix/profiles/default/bin", e.get("PATH", "")])
    return e


def which(cmd):
    return shutil.which(cmd, path=env_path()["PATH"])


def run(cmd, check=True, capture=False, cwd=None):
    log("$", cmd if isinstance(cmd, str) else " ".join(map(str, cmd)))
    r = subprocess.run(cmd, shell=isinstance(cmd, str), env=env_path(), text=True, cwd=cwd,
                       capture_output=capture)
    if check and r.returncode:
        sys.exit(f"command failed ({r.returncode})")
    return r


def out(cmd):
    try:
        r = subprocess.run(cmd, env=env_path(), text=True, capture_output=True, timeout=60)
        return (r.stdout or r.stderr).strip().splitlines()[0] if r.returncode == 0 else None
    except Exception:
        return None


def versions():
    return tomllib.loads((PIPE / "toolchain/versions.toml").read_text())


def mathlib_key():
    v = versions()
    return f"aeneas-{v['aeneas']['commit'][:7]}-lean-{v['lean']['version']}"


def find_mathlib_cache():
    """Where the engine keeps mathlib: one shared copy per key in $VPIPE_HOME/lake/<key>/, filled
    from a tarball in a cache dir, `lake exe cache get`, or (last resort) a source build."""
    v = versions()
    shared = VH / "lake" / mathlib_key() / ".lake/packages/mathlib/.lake/build"
    hits = [str(shared.parent.parent)] if shared.exists() else []
    dirs = os.environ.get("VPIPE_CACHE_DIRS", "").split(os.pathsep) if os.environ.get("VPIPE_CACHE_DIRS") \
        else v["mathlib"]["cache_dirs"]
    short = v["aeneas"]["commit"][:7]
    for d in dirs:
        d = Path(d) if Path(d).is_absolute() else PIPE / d
        if d.exists():
            hits += [str(p) for p in sorted(d.glob(f"*{mathlib_key()}*.tar*")) or sorted(d.glob(f"*{short}*mathlib*.tar*"))
                     if not p.name.endswith(".part")]
    return hits


def vpipe(*args):
    return subprocess.call([sys.executable, str(PIPE / "bin/vpipe.py"), *args], env=env_path())


def confirm(plan, yes):
    print("\nPlanned changes:")
    for p in plan:
        print("  -", p)
    if yes:
        return True
    if not sys.stdin.isatty():
        sys.exit("\nNo terminal to ask for approval. Re-run with --yes to apply this plan.")
    return input("\nApply? [y/N] ").strip().lower() in ("y", "yes")


# ------------------------------------------------------------------ doctor
def reachable(host):
    # Through a proxy, a TCP check says nothing; use curl so proxy rules apply.
    if which("curl"):
        r = subprocess.run(["curl", "-sS", "-o", "/dev/null", "-m", "8", "-w", "%{http_code}", f"https://{host}/"],
                           capture_output=True, text=True)
        code = r.stdout.strip()
        return code not in ("", "000", "403", "407") and r.returncode == 0
    try:
        socket.create_connection((host, 443), timeout=5).close()
        return True
    except OSError:
        return False


def doctor(as_json=False):
    v = versions()
    sysinfo = {"os": platform.system(), "arch": platform.machine(), "python": platform.python_version()}
    tools = {
        "git": out(["git", "--version"]),
        "curl": out(["curl", "--version"]),
        "zstd": out(["zstd", "--version"]),
        "rustup": out(["rustup", "--version"]),
        "elan": out(["elan", "--version"]),
        "lean": out(["lean", "--version"]),
        "lake": out(["lake", "--version"]),
        "aeneas": "found" if which("aeneas") else None,
        "charon": out(["charon", "version"]) or ("found" if which("charon") else None),
        "frama-c": out(["frama-c", "-version"]),
        "why3": out(["why3", "--version"]),
        "z3": out(["z3", "--version"]),
        "cvc5": out(["cvc5", "--version"]),
        "cbmc": out(["cbmc", "--version"]),
        "nix": out(["nix", "--version"]),
        "opam": out(["opam", "--version"]),
        "docker": out(["docker", "--version"]),
        "claude": out(["claude", "--version"]),
        "codex": out(["codex", "--version"]),
        "gemini": out(["gemini", "--version"]),
    }
    pins = {"aeneas": v["aeneas"]["tag"], "lean": v["lean"]["version"]}
    installed = {}
    if (VH / "installed.json").exists():
        installed = json.loads((VH / "installed.json").read_text())
    cache = find_mathlib_cache()
    net = {h: reachable(h) for h in HOSTS}
    skills = {a: sorted(p.name for p in d.glob("*") if (p / ".vkit-skill").exists()) if d.exists() else []
              for a, d in AGENT_SKILL_DIRS.items()}
    problems = []
    for d in LEGACY_SKILL_DIRS:
        old = [p.name for p in d.glob("*") if (p / ".vkit-skill").exists()] if d.exists() else []
        if old:
            problems.append(f"old vkit skill copies in {d} ({len(old)}); current Codex reads ~/.agents/skills, "
                            f"so remove them to avoid duplicates: rm -r {d}/{{{','.join(old)}}}")
    if sysinfo["os"] != "Linux":
        problems.append("Aeneas ships Linux binaries only; on macOS/Windows use the dev container (docs/installation.md).")
    if installed.get("aeneas") and installed["aeneas"] != pins["aeneas"]:
        problems.append(f"installed Aeneas {installed['aeneas']} differs from the pin {pins['aeneas']}: run `vkit setup lean`.")
    if tools["lean"] and pins["lean"] not in tools["lean"]:
        problems.append(f"default `lean` is not {pins['lean']}; projects pick the right one through lean-toolchain, so this is only a note.")
    if not cache and not net["cache.mathlib.org"]:
        problems.append("no mathlib cache and cache.mathlib.org unreachable: the first Lean build compiles mathlib (hours).")
    if not (tools["frama-c"] or tools["nix"] or tools["opam"] or tools["docker"]):
        problems.append("no route to Frama-C: install Nix (recommended), opam, or Docker.")
    rep = {"system": sysinfo, "pins": pins, "installed": installed, "tools": tools,
           "mathlib_cache": cache, "network": net, "skills": skills, "problems": problems,
           "engine_version": (PIPE / "VERSION").read_text().strip()}
    if as_json:
        print(json.dumps(rep, indent=1))
        return 0 if not problems else 1
    print(f"vkit doctor  (engine {rep['engine_version']}, {sysinfo['os']} {sysinfo['arch']}, Python {sysinfo['python']})")
    print(f"pins: Aeneas {pins['aeneas']}, Lean {pins['lean']}")
    print("\ntools:")
    for k, val in tools.items():
        print(f"  {'ok ' if val else '-- '} {k:9} {val or 'not found'}")
    print("\nnetwork:")
    for h, ok in net.items():
        print(f"  {'ok ' if ok else 'NO '} {h:24} {'' if ok else 'needed for ' + HOSTS[h]}")
    print("\nmathlib cache:", cache[0] if cache else "none")
    print("skills:", ", ".join(f"{a}: {len(s)}" for a, s in skills.items()))
    print("\n" + ("problems:\n" + "\n".join("  - " + p for p in problems) if problems else "no problems found"))
    return 0 if not problems else 1


# ------------------------------------------------------------------ setup
def pkg_install_hint(pkg):
    sudo = "" if os.geteuid() == 0 else "sudo "
    if which("nix"):  # no root needed, and the binary cache is fast
        return (f"mkdir -p {VH}/bin && ln -sf \"$(nix --extra-experimental-features 'nix-command flakes' "
                f"build --no-link --print-out-paths nixpkgs#{pkg}.bin)/bin/{pkg}\" {VH}/bin/{pkg}")
    if which("apt-get"):
        return f"{sudo}apt-get update -qq && {sudo}apt-get install -y {pkg}"
    if which("brew"):
        return f"brew install {pkg}"
    if which("dnf"):
        return f"{sudo}dnf install -y {pkg}"
    return f"install {pkg} with your package manager"


def setup_lean(yes):
    plan, pre = [], []
    if platform.system() != "Linux":
        sys.exit("Aeneas release binaries are Linux-only. Use the dev container instead (docs/installation.md).")
    if not which("zstd"):
        pre.append(pkg_install_hint("zstd"))
    if not which("rustup"):
        pre.append("curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain none")
    v = versions()
    plan += [*(f"run: {c}" for c in pre),
             f"download Aeneas + Charon {v['aeneas']['tag']} into {VH}/",
             "install the Rust nightly Charon needs (rustup), plus the riscv64 no_std target",
             f"install elan (if missing) and Lean {v['lean']['version']} into ~/.elan",
             "then: vkit setup mathlib (prebuilt mathlib for the pinned Lean)"]
    if not confirm(plan, yes):
        return 1
    for c in pre:
        run(c)
    if vpipe("setup", "lean"):
        return 1
    return setup_mathlib(True)


def setup_mathlib(yes):
    """Get mathlib for the pinned Lean once, by building the engine's Lean fixture. The engine
    restores a cached tarball, else runs `lake exe cache get`, else compiles mathlib."""
    if find_mathlib_cache():
        log(f"mathlib already available: {find_mathlib_cache()[0]}")
        return 0
    net = reachable("cache.mathlib.org")
    plan = [f"build the engine's Lean fixture once (vpipe check-fixture rust --full)",
            "mathlib: " + ("download prebuilt files from cache.mathlib.org (~2 min)" if net else
                           "cache.mathlib.org unreachable, so mathlib compiles from source (hours, ~8 GB RAM)"),
            f"keep one shared copy in {VH}/lake/{mathlib_key()}/ (~2.5 GB), linked into every Lean project"]
    if not confirm(plan, yes):
        return 1
    r = subprocess.run([sys.executable, str(PIPE / "bin/vpipe.py"), "check-fixture", "rust", "--full"],
                       env=env_path(), text=True, stdout=subprocess.PIPE)
    try:
        ok = json.loads(r.stdout.strip().splitlines()[-1]).get("ok")
    except Exception:
        ok = False
    if not ok:
        log("the Lean fixture did not build; see the engine output above")
        return 1
    if find_mathlib_cache():
        log(f"mathlib ready: {find_mathlib_cache()[0]}")
    else:
        log("Lean fixture built. mathlib comes from cache.mathlib.org per project (~2 min each).")
    return 0


def setup_framac(yes):
    v = versions()
    if which("nix"):
        if not confirm([f"nix build {', '.join(v['framac']['nix_packages'])} from cache.nixos.org, link into {VH}/bin",
                        "why3 config detect"], yes):
            return 1
        return vpipe("setup", "framac")
    if which("opam"):
        plan = ["opam install -y frama-c why3 alt-ergo z3 (inside your current opam switch; compiles OCaml, 10-30 min)",
                "why3 config detect"]
        if not confirm(plan, yes):
            return 1
        run("opam install -y frama-c why3 alt-ergo z3")
        run("eval $(opam env) && why3 config detect", check=False)
        return 0
    sys.exit("No Nix or opam found. Easiest: install Nix (https://nixos.org/download) and re-run, "
             "or use the dev container (docs/installation.md).")


def setup_cbmc(yes):
    if which("cbmc"):
        log("cbmc already installed:", out(["cbmc", "--version"]))
        return 0
    ver = "6.4.1"
    if platform.system() == "Darwin" and which("brew"):
        cmd = "brew install cbmc"
    elif platform.system() == "Linux" and which("dpkg") and platform.machine() == "x86_64":
        deb = f"ubuntu-24.04-cbmc-{ver}-Linux.deb"
        sudo = "" if os.geteuid() == 0 else "sudo "
        # apt installs the .deb with its dependencies (bash-completion); dpkg -i alone does not.
        cmd = (f"cd /tmp && curl -fsSLO https://github.com/diffblue/cbmc/releases/download/cbmc-{ver}/{deb} && "
               f"{sudo}apt-get update -qq && {sudo}apt-get install -y ./{deb}")
    elif which("nix"):
        cmd = f"nix profile install nixpkgs#cbmc"
    else:
        sys.exit("No supported route to CBMC here; see https://github.com/diffblue/cbmc/releases")
    if not confirm([f"run: {cmd}"], yes):
        return 1
    run(cmd)
    if not out(["cbmc", "--version"]):
        sys.exit("cbmc still not runnable after install; see the output above")
    log("cbmc", out(["cbmc", "--version"]))
    return 0


# ------------------------------------------------------------------ skills
def skill_names():
    return sorted(p.parent.name for p in SKILLS.glob("*/SKILL.md"))


def install_skills(agents, yes, dry):
    targets = []
    for a in agents:
        d = AGENT_SKILL_DIRS.get(a, Path(a).expanduser())
        if d not in targets:  # codex and gemini share ~/.agents/skills
            targets.append(d)
    plan = []
    for d in targets:
        for n in skill_names():
            dest = d / n
            if dest.exists() and not (dest / ".vkit-skill").exists():
                plan.append(f"{dest} exists and was not installed by vkit: back it up to {dest}.bak-<time>, then replace")
            else:
                plan.append(f"copy skills/{n} -> {dest}")
    if dry:
        print("\n".join(plan))
        return 0
    if not confirm(plan, yes):
        return 1
    stamp = time.strftime("%Y%m%d%H%M%S")
    for d in targets:
        d.mkdir(parents=True, exist_ok=True)
        for n in skill_names():
            dest = d / n
            if dest.exists():
                if (dest / ".vkit-skill").exists():
                    shutil.rmtree(dest)
                else:
                    dest.rename(d / f"{n}.bak-{stamp}")
            shutil.copytree(SKILLS / n, dest)
            (dest / ".vkit-skill").write_text(json.dumps({"source": str(REPO), "installed": stamp}))
    log("skills installed; restart your agent so it picks them up")
    return 0


def update():
    if (REPO / ".git").exists():
        run(["git", "-C", str(REPO), "pull", "--ff-only"])
    agents = [a for a, d in AGENT_SKILL_DIRS.items() if any((p / ".vkit-skill").exists() for p in d.glob("*"))]
    agents = list(dict.fromkeys(str(AGENT_SKILL_DIRS[a]) for a in agents))
    return install_skills(agents, True, False) if agents else 0


def main():
    known = {"doctor", "setup", "skills", "update", "-h", "--help"}
    if len(sys.argv) > 2 and sys.argv[1] == "new":
        rc = vpipe(*sys.argv[1:])
        claim = PIPE / "libraries" / sys.argv[2] / "CLAIM.md"
        if rc == 0 and claim.parent.exists() and not claim.exists():
            shutil.copy(SKILLS / "verify-library/templates/CLAIM.md", claim)
            log(f"wrote {claim}: fill sections 1-2 (target, success criteria) and get them approved first")
        sys.exit(rc)
    if len(sys.argv) > 1 and sys.argv[1] not in known:
        sys.exit(vpipe(*sys.argv[1:]))
    ap = argparse.ArgumentParser(prog="vkit", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    s = ap.add_subparsers(dest="cmd")
    d = s.add_parser("doctor"); d.add_argument("--json", action="store_true")
    st = s.add_parser("setup"); st.add_argument("which", nargs="?", default="all",
                                                choices=["lean", "framac", "cbmc", "mathlib", "all"])
    st.add_argument("--yes", "-y", action="store_true")
    sk = s.add_parser("skills"); sk.add_argument("action", choices=["install", "list"])
    sk.add_argument("--agent", action="append", help="claude, codex, gemini, or a directory (repeatable)")
    sk.add_argument("--yes", "-y", action="store_true"); sk.add_argument("--dry-run", action="store_true")
    s.add_parser("update")
    a = ap.parse_args()
    if a.cmd == "doctor":
        return doctor(a.json)
    if a.cmd == "setup":
        steps = {"lean": setup_lean, "framac": setup_framac, "cbmc": setup_cbmc, "mathlib": setup_mathlib}
        order = ["lean", "framac", "cbmc"] if a.which == "all" else [a.which]
        return max(steps[w](a.yes) or 0 for w in order)
    if a.cmd == "skills":
        if a.action == "list":
            print("\n".join(skill_names()))
            return 0
        return install_skills(a.agent or ["claude"], a.yes, a.dry_run)
    if a.cmd == "update":
        return update()
    ap.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
