#!/usr/bin/env python3
"""open-proofs checker driver. The checker is the review: nothing else vouches for a result.

For each claim it runs five layers and passes only if all pass:

  1. integrity    pinned upstream commit, toolchain, clean dependency checkouts, and a
                  lakefile without options that could weaken checking.
  2. lint         source-level bans (sorry, axioms, native_decide, implemented_by/extern/
                  opaque, metaprogramming, notation, ...) and an import allowlist.
  3. build        `lake build` of the result module (and of a variant's statement module),
                  after deleting the candidate modules' build outputs so the .olean files
                  come from the current source.
  4. opcheck      Lean-level checks on the compiled environment (see
                  OpenProofsChecker/Main.lean): statement identical (as an `Expr`) to the
                  pinned reference, axioms in {propext, Classical.choice, Quot.sound} by a full
                  body walk, no axiom/opaque/unsafe/partial/implemented_by/extern/export/init
                  declarations, no shadowing, everything under `OpenProofs.`, kernel replay.
  5. leanchecker  an independent kernel replay of every candidate module with the
                  toolchain's own `leanchecker`.

Usage:
  python3 scripts/check.py --claim ID [--record]     check one claim from claims.json
  python3 scripts/check.py --all [--record]          check every claim
  python3 scripts/check.py --adhoc --module M --theorem T --ref-module RM --ref-theorem R
                           [--ref-kind upstream|variant]
  python3 scripts/check.py --integrity               only the integrity layer

`--record` writes the verdicts to ledger/results.json and regenerates ledger/LEDGER.md.
Exit code 0 iff every checked claim passes.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lint as lintmod  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
ELAN_BIN = Path.home() / ".elan" / "bin"
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
TRUSTED_BASE = [
    "lakefile.toml",
    "lean-toolchain",
    "lake-manifest.json",
    "upstream.json",
    "OpenProofsChecker",
    "scripts/check.py",
    "scripts/lint.py",
]
FORBIDDEN_LAKEFILE_KEYS = [
    "moreLeanArgs", "weakLeanArgs", "moreServerArgs", "moreServerOptions", "moreGlobalServerArgs",
    "plugins", "dynlibs", "loadDynlibPaths", "precompileModules", "moreLinkArgs", "moreLinkObjs",
    "extraDepTargets", "moreLeancArgs", "weakLeancArgs", "nativeFacets",
]


def env() -> dict:
    e = dict(os.environ)
    e["PATH"] = f"{ELAN_BIN}:{e.get('PATH', '')}"
    return e


def run(cmd: list[str], cwd: Path, timeout: int = 3600) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env(), capture_output=True, text=True, timeout=timeout)
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired as e:
        return 124, f"timeout after {timeout}s: {e}"


def layer(name: str, ok: bool, detail, **extra) -> dict:
    d = {"layer": name, "ok": bool(ok), "detail": detail}
    d.update(extra)
    return d


# ---------------------------------------------------------------------------- integrity


def lakefile_problems(text: str) -> list[str]:
    probs = []
    for key in FORBIDDEN_LAKEFILE_KEYS:
        if re.search(rf"^\s*{key}\s*=", text, re.MULTILINE):
            probs.append(f"lakefile sets forbidden key `{key}`")
    for pat in (r"debug\.", r"skipKernelTC", r"trustLevel", r"\btrust\b"):
        if re.search(pat, text):
            probs.append(f"lakefile mentions `{pat}`")
    return probs


def integrity(root: Path = ROOT, pkgs_dir: Path | None = None) -> dict:
    probs: list[str] = []
    up = json.loads((root / "upstream.json").read_text())
    pinned = up["formal_conjectures"]["commit"]
    toolchain = (root / "lean-toolchain").read_text().strip()
    if toolchain != up["lean_toolchain"]:
        probs.append(f"lean-toolchain {toolchain!r} != upstream.json {up['lean_toolchain']!r}")
    if (root / "lakefile.lean").exists():
        probs.append("lakefile.lean exists (Lean-code lakefiles can run arbitrary code)")
    lakefile = (root / "lakefile.toml").read_text()
    probs += lakefile_problems(lakefile)
    m = re.search(r'name\s*=\s*"formal_conjectures"[^\[]*?rev\s*=\s*"([0-9a-f]+)"', lakefile, re.S)
    if not m or m.group(1) != pinned:
        probs.append(f"lakefile formal_conjectures rev {m.group(1) if m else None} != pinned {pinned}")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    pkgs_dir = pkgs_dir or (root / ".lake" / "packages")
    by_name = {p["name"]: p for p in manifest["packages"]}
    fc = by_name.get("formal_conjectures")
    if not fc or fc["rev"] != pinned:
        probs.append(f"manifest formal_conjectures rev {fc and fc['rev']} != pinned {pinned}")
    if "mathlib" in by_name and by_name["mathlib"]["rev"] != up.get("mathlib_rev"):
        probs.append(f"manifest mathlib rev {by_name['mathlib']['rev']} != upstream.json {up.get('mathlib_rev')}")
    pkg_states = {}
    for name, p in by_name.items():
        d = pkgs_dir / name
        if not d.is_dir():
            probs.append(f"package {name} missing at {d}")
            continue
        rc, head = run(["git", "-C", str(d), "rev-parse", "HEAD"], root)
        head = head.strip()
        if rc != 0 or head != p["rev"]:
            probs.append(f"package {name} HEAD {head} != manifest {p['rev']}")
        rc, st = run(["git", "-C", str(d), "status", "--porcelain", "--untracked-files=all"], root)
        if rc != 0 or st.strip():
            probs.append(f"package {name} working tree not clean: {st.strip()[:300]}")
        pkg_states[name] = head
    if fc:
        up_tc = (pkgs_dir / "formal_conjectures" / "lean-toolchain")
        if up_tc.exists() and up_tc.read_text().strip() != toolchain:
            probs.append(f"upstream lean-toolchain {up_tc.read_text().strip()} != ours {toolchain}")
    return layer("integrity", not probs, probs or "pinned upstream, clean packages, safe lakefile",
                 upstream_commit=pinned, toolchain=toolchain, packages=pkg_states)


def trusted_base_hash(root: Path = ROOT) -> str:
    h = hashlib.sha256()
    for item in TRUSTED_BASE:
        p = root / item
        files = sorted(p.rglob("*")) if p.is_dir() else [p]
        for f in files:
            if f.is_file() and "__pycache__" not in f.parts:
                h.update(str(f.relative_to(root)).encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()


def repo_state(root: Path = ROOT) -> dict:
    _, head = run(["git", "rev-parse", "HEAD"], root)
    _, st = run(["git", "status", "--porcelain"], root)
    return {"commit": head.strip(), "dirty": bool(st.strip())}


# ---------------------------------------------------------------------------- layers


def lint_layer(root: Path, module: str, ref_module: str | None, ref_kind: str) -> dict:
    findings = []
    files = lintmod.source_closure(root, module)
    missing = [str(p) for p in files if not p.exists()]
    for p in files:
        if p.exists():
            findings += [f.to_json() for f in lintmod.lint_file(p, lintmod.role_of(p, root), root)]
    if ref_kind == "variant" and ref_module:
        sp = lintmod.module_path(root, ref_module)
        if sp.exists():
            findings += [f.to_json() for f in lintmod.lint_file(sp, "statement", root)]
        else:
            missing.append(str(sp))
    probs = findings + [{"rule": "missing source", "file": m} for m in missing]
    return layer("lint", not probs, probs or f"{len(files)} file(s) clean")


def clean_outputs(root: Path, modules: list[str]) -> None:
    """Delete build outputs of candidate modules so they are rebuilt from source."""
    for m in modules:
        rel = Path(*[c.strip("«»") for c in m.split(".")])
        for base in (root / ".lake" / "build" / "lib" / "lean", root / ".lake" / "build" / "ir"):
            d = (base / rel).parent
            if d.is_dir():
                for f in d.glob(rel.name + ".*"):
                    f.unlink()


def build_layer(root: Path, targets: list[str]) -> dict:
    rc, out = run(["lake", "build", *targets], root)
    tail = "\n".join(l for l in out.splitlines() if not l.startswith(("✔", "⣿", "info: ")))[-4000:]
    warn_sorry = "declaration uses 'sorry'" in out or "declaration uses `sorry`" in out
    return layer("build", rc == 0, tail.strip() or "ok", exit_code=rc, sorry_warning=warn_sorry)


def opcheck_layer(root: Path, claim: dict, replay: bool = True) -> dict:
    cmd = ["lake", "exe", "opcheck", "--module", claim["module"], "--theorem", claim["theorem"],
           "--ref-module", claim["ref_module"], "--ref-theorem", claim["ref_theorem"],
           "--ref-kind", claim.get("ref_kind", "upstream")]
    if not replay:
        cmd.append("--no-replay")
    rc, out = run(cmd, root)
    js = None
    for line in out.splitlines()[::-1]:
        line = line.strip()
        if line.startswith("{") and line.endswith("}"):
            try:
                js = json.loads(line)
                break
            except json.JSONDecodeError:
                pass
    if js is None:
        return layer("opcheck", False, f"no JSON from opcheck (exit {rc}): {out[-2000:]}", checks=[])
    ok = rc == 0 and js.get("verdict") == "PASS"
    failed = [c["name"] for c in js.get("checks", []) if not c["ok"]]
    return layer("opcheck", ok, "all Lean-level checks passed" if ok else f"failed: {failed}",
                 checks=js.get("checks", []), axioms=js.get("axioms", []),
                 candidate_modules=js.get("candidate_modules", []), lean_version=js.get("lean_version"),
                 statement_identity=js.get("statement_identity"), ref_axioms=js.get("ref_axioms"))


def leanchecker_layer(root: Path, modules: list[str]) -> dict:
    if not modules:
        return layer("leanchecker", False, "no candidate modules to replay")
    errs = []
    for m in modules:
        rc, out = run(["lake", "env", "leanchecker", m], root)
        if rc != 0:
            errs.append(f"{m}: exit {rc}: {out.strip()[-1500:]}")
    return layer("leanchecker", not errs, errs or f"replayed {len(modules)} module(s)")


# ---------------------------------------------------------------------------- statement text


def decl_source(root: Path, module: str, decl: str, upstream: bool) -> dict:
    """Best-effort source text of a declaration's statement, for the human-readable ledger."""
    import triage  # local import; triage is not part of the trusted base

    base = root / ".lake" / "packages" / "formal_conjectures" if upstream else root
    path = lintmod.module_path(base, module)
    if not path.exists():
        return {}
    for d in triage.parse_file(path):
        if d["decl"] == decl:
            return {"file": str(path.relative_to(base)), "line": d["line"], "statement": d["statement"],
                    "category": d["category"], "formal_proof": d["formal_proof"], "sorry": d["sorry"]}
    return {"file": str(path.relative_to(base))}


# ---------------------------------------------------------------------------- driver


def check_claim(claim: dict, root: Path = ROOT, clean: bool = True, replay: bool = True,
                skip_integrity: bool = False) -> dict:
    kind = claim.get("ref_kind", "upstream")
    layers = []
    if not skip_integrity:
        layers.append(integrity(root))
    layers.append(lint_layer(root, claim["module"], claim["ref_module"], kind))
    # Candidate modules reachable through source imports: their outputs are rebuilt.
    src_mods = [".".join(p.relative_to(root).with_suffix("").parts)
                for p in lintmod.source_closure(root, claim["module"]) if p.exists()]
    targets = [claim["module"], claim["ref_module"]]
    if kind == "variant":
        src_mods.append(claim["ref_module"])
    if clean:
        clean_outputs(root, sorted(set(src_mods)))
    b = build_layer(root, targets + ["opcheck"])
    layers.append(b)
    if b["ok"]:
        oc = opcheck_layer(root, claim, replay=replay)
        layers.append(oc)
        layers.append(leanchecker_layer(root, oc.get("candidate_modules") or [claim["module"]]))
    else:
        layers.append(layer("opcheck", False, "skipped: build failed", checks=[]))
        layers.append(layer("leanchecker", False, "skipped: build failed"))
    verdict = "PASS" if all(l["ok"] for l in layers) else "FAIL"
    up = json.loads((root / "upstream.json").read_text())
    return {
        "id": claim.get("id", "adhoc"),
        "verdict": verdict,
        "checked_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "upstream_commit": up["formal_conjectures"]["commit"],
        "toolchain": up["lean_toolchain"],
        "trusted_base_sha256": trusted_base_hash(root),
        "repo": repo_state(root),
        "axioms": next((l.get("axioms") for l in layers if l["layer"] == "opcheck"), None),
        "statement_identity": next((l.get("statement_identity") for l in layers if l["layer"] == "opcheck"), None),
        "ref_axioms": next((l.get("ref_axioms") for l in layers if l["layer"] == "opcheck"), None),
        "layers": layers,
    }


def load_claims(root: Path = ROOT) -> list[dict]:
    return json.loads((root / "claims.json").read_text())["claims"]


def record(reports: list[dict], root: Path = ROOT) -> None:
    path = root / "ledger" / "results.json"
    data = json.loads(path.read_text()) if path.exists() else {"results": {}}
    claims = {c["id"]: c for c in load_claims(root)}
    for r in reports:
        c = claims.get(r["id"], {})
        upstream = c.get("ref_kind", "upstream") == "upstream"
        entry = {
            "claim": c,
            "reference_source": decl_source(root, c.get("ref_module", ""), c.get("ref_theorem", ""), upstream)
            if c else {},
            "check": r,
        }
        data["results"][r["id"]] = entry
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    render_ledger(root)


def render_ledger(root: Path = ROOT) -> None:
    data = json.loads((root / "ledger" / "results.json").read_text())
    rows = []
    for rid, e in sorted(data["results"].items()):
        c, r, src = e["claim"], e["check"], e.get("reference_source", {})
        failed = [l["layer"] for l in r["layers"] if not l["ok"]]
        rows.append(
            f"| `{rid}` | {c.get('tier', '?')} | {c.get('assessment', '?')} | **{r['verdict']}**"
            f"{' (' + ', '.join(failed) + ')' if failed else ''} | `{c.get('ref_theorem')}` "
            f"({c.get('ref_kind', 'upstream')}; upstream category: {src.get('category')}; "
            f"identity: {r.get('statement_identity')}) | "
            f"{', '.join(r.get('axioms') or [])} | {r['upstream_commit'][:12]} | {r['checked_at'][:10]} |"
        )
    md = [
        "# Results ledger",
        "",
        "Generated by `python3 scripts/check.py --all --record` from `ledger/results.json`. Do not edit by hand.",
        "",
        "Verdict PASS means all five checker layers passed (integrity, lint, build, opcheck, leanchecker).",
        "The assessment column is the claim's own classification (see `claims.json`); a PASS on a",
        "`possible-misformalization` claim means the *formal* statement is proved, not the informal problem.",
        "",
        "| id | tier | assessment | verdict | reference | axioms | upstream | checked |",
        "|---|---|---|---|---|---|---|---|",
        *rows,
        "",
    ]
    (root / "ledger" / "LEDGER.md").write_text("\n".join(md))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--claim")
    g.add_argument("--all", action="store_true")
    g.add_argument("--adhoc", action="store_true")
    g.add_argument("--integrity", action="store_true")
    ap.add_argument("--module")
    ap.add_argument("--theorem")
    ap.add_argument("--ref-module")
    ap.add_argument("--ref-theorem")
    ap.add_argument("--ref-kind", default="upstream", choices=["upstream", "variant"])
    ap.add_argument("--record", action="store_true")
    ap.add_argument("--no-clean", action="store_true")
    ap.add_argument("--json", action="store_true", help="print full JSON reports")
    args = ap.parse_args()

    if args.integrity:
        r = integrity(ROOT)
        print(json.dumps(r, indent=1, ensure_ascii=False))
        return 0 if r["ok"] else 1
    if args.adhoc:
        claims = [{"id": "adhoc", "module": args.module, "theorem": args.theorem,
                   "ref_module": args.ref_module, "ref_theorem": args.ref_theorem,
                   "ref_kind": args.ref_kind}]
    else:
        claims = load_claims(ROOT)
        if args.claim:
            claims = [c for c in claims if c["id"] == args.claim]
            if not claims:
                print(f"no claim {args.claim!r} in claims.json", file=sys.stderr)
                return 2
    reports = []
    for c in claims:
        r = check_claim(c, ROOT, clean=not args.no_clean)
        reports.append(r)
        failed = [l["layer"] for l in r["layers"] if not l["ok"]]
        print(f"{r['verdict']}  {c['id']}  axioms={r['axioms']}  identity={r['statement_identity']}"
              + (f"  failed={failed}" if failed else ""))
        if args.json or r["verdict"] != "PASS":
            for l in r["layers"]:
                if not l["ok"] or args.json:
                    print(json.dumps(l, indent=1, ensure_ascii=False)[:6000])
    if args.record and not args.adhoc:
        record(reports, ROOT)
    return 0 if all(r["verdict"] == "PASS" for r in reports) else 1


if __name__ == "__main__":
    sys.exit(main())
