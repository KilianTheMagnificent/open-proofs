#!/usr/bin/env python3
"""Quick-kill sweep: throw cheap automation at upstream placeholder statements and their negations.

For every placeholder theorem in the selected upstream files it tries, under a small heartbeat
budget, `omega | decide | norm_num | simp | trivial | aesop` on the statement P and on ¬P.

Why: an open research problem should never fall to these tactics. A hit on P or ¬P for a
`research open` statement is a strong *possible misformalization* signal (vacuous hypotheses,
`sSup`/`iSup` of an unbounded set being 0 in ℕ, natural subtraction, empty ranges, ...). A hit on
a `research solved`/`textbook` statement is a cheap tier-(b) candidate. Every hit needs a human-
style look at the informal problem before anything is claimed; the sweep only produces leads.

The sweep is NOT part of the trusted checker. Real claims still go through scripts/check.py.

Usage:
  python3 scripts/quickkill.py --subdir ErdosProblems [--limit N] [--workers 4] [--resume]
  python3 scripts/quickkill.py --files ErdosProblems/123.lean ErdosProblems/456.lean
Outputs: work/quickkill/<stem>.lean (generated), work/quickkill/results.jsonl (one line per attempt),
and a summary of hits on stdout. Requires the upstream modules to be built (`lake build <module>`).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import triage  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
UP = ROOT / ".lake" / "packages" / "formal_conjectures"
OUT = ROOT / "work" / "quickkill"
TACTICS = "first | omega | decide | norm_num | simp | trivial | aesop"


def env() -> dict:
    e = dict(os.environ)
    e["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{e.get('PATH', '')}"
    return e


def lean_name(decl: str) -> str:
    # Escape components that are not plain identifiers (already-escaped ones are kept).
    parts = re.findall(r"«[^»]*»|[^.]+", decl)
    out = []
    for p in parts:
        if p.startswith("«") or re.match(r"^[A-Za-z_][A-Za-z0-9_'!?₀-₉ₐ-ₜ]*$", p):
            out.append(p)
        else:
            out.append(f"«{p}»")
    return ".".join(out)


def gen_file(path: Path, decls: list[dict], heartbeats: int) -> tuple[Path, list[dict]]:
    module = triage.module_name(path)
    lines = [f"import {module}", "", "set_option linter.all false", f"set_option maxHeartbeats {heartbeats}", "",
             "namespace OpenProofs.QK", ""]
    attempts = []
    for i, d in enumerate(decls):
        n = lean_name(d["decl"])
        for direction, ty in (("pos", f"type_of% @{n}"), ("neg", f"¬ (type_of% @{n})")):
            name = f"qk_{direction}_{i}"
            start = len(lines) + 1
            lines.append(f"theorem {name} : {ty} := by")
            lines.append(f"  {TACTICS}")
            lines.append("")
            attempts.append({"decl": d["decl"], "category": d["category"], "direction": direction,
                             "thm": f"OpenProofs.QK.{name}", "start": start, "end": start + 1})
    lines.append("end OpenProofs.QK")
    lines.append("")
    for a in attempts:
        lines.append(f"#print axioms {a['thm']}")
    OUT.mkdir(parents=True, exist_ok=True)
    rel = path.relative_to(UP / "FormalConjectures")
    gen = OUT / ("_".join(rel.with_suffix("").parts) + ".lean")
    gen.write_text("\n".join(lines) + "\n")
    return gen, attempts


def run_file(path: Path, decls: list[dict], heartbeats: int, timeout: int) -> list[dict]:
    gen, attempts = gen_file(path, decls, heartbeats)
    try:
        p = subprocess.run(["lake", "env", "lean", str(gen)], cwd=ROOT, env=env(), capture_output=True,
                           text=True, timeout=timeout)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return [dict(a, file=str(path.relative_to(UP)), ok=False, note="file timeout") for a in attempts]
    err_lines = {int(m.group(1)) for m in re.finditer(rf"{re.escape(gen.name)}:(\d+):\d+: error", out)}
    import_fail = any(l < 6 for l in err_lines) or "unknown module prefix" in out or "object file" in out
    axioms = {}
    for m in re.finditer(r"'(OpenProofs\.QK\.qk_\w+)' depends on axioms: \[([^\]]*)\]", out):
        axioms[m.group(1)] = [x.strip() for x in m.group(2).split(",") if x.strip()]
    for m in re.finditer(r"'(OpenProofs\.QK\.qk_\w+)' does not depend on any axioms", out):
        axioms[m.group(1)] = []
    res = []
    for a in attempts:
        errs = [l for l in err_lines if a["start"] <= l <= a["end"]]
        ax = axioms.get(a["thm"])
        ok = (not import_fail) and not errs and ax is not None and "sorryAx" not in ax
        res.append({"file": str(path.relative_to(UP)), "decl": a["decl"], "category": a["category"],
                    "direction": a["direction"], "ok": ok, "axioms": ax,
                    "note": "import failed" if import_fail else ("error" if errs else "")})
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--subdir", help="subdirectory of FormalConjectures/, e.g. ErdosProblems")
    ap.add_argument("--files", nargs="*", help="paths relative to FormalConjectures/")
    ap.add_argument("--categories", default="research open,research solved,textbook,test,API")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--heartbeats", type=int, default=40000)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--resume", action="store_true", help="skip files already in results.jsonl")
    args = ap.parse_args()
    cats = {c.strip() for c in args.categories.split(",")}
    base = UP / "FormalConjectures"
    if args.files:
        paths = [base / f for f in args.files]
    else:
        paths = sorted((base / args.subdir).rglob("*.lean"),
                       key=lambda p: (int(p.stem) if p.stem.isdigit() else 10**9, p.name))
    OUT.mkdir(parents=True, exist_ok=True)
    resf = OUT / "results.jsonl"
    done = set()
    if args.resume and resf.exists():
        done = {json.loads(l)["file"] for l in resf.read_text().splitlines() if l.strip()}
    jobs = []
    for p in paths:
        if str(p.relative_to(UP)) in done:
            continue
        decls = [d for d in triage.parse_file(p) if d["sorry"] and d["category"] in cats]
        if decls:
            jobs.append((p, decls))
    if args.limit:
        jobs = jobs[: args.limit]
    print(f"{len(jobs)} file(s), {sum(len(d) for _, d in jobs)} statement(s)")
    hits = []
    with ThreadPoolExecutor(max_workers=args.workers) as ex, resf.open("a") as fh:
        for res in ex.map(lambda j: run_file(j[0], j[1], args.heartbeats, args.timeout), jobs):
            for r in res:
                fh.write(json.dumps(r, ensure_ascii=False) + "\n")
                if r["ok"]:
                    hits.append(r)
                    print(f"HIT {r['direction']}  {r['category']:<16} {r['decl']}  ({r['file']})", flush=True)
            fh.flush()
    print(f"{len(hits)} hit(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
