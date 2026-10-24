#!/usr/bin/env python3
"""Adversarial test suite: proves the checker rejects each known cheat.

Three groups:
  * lean     -- cheat modules in tests/adversarial/cases/, run through the full checker
               (scripts/check.py). Each case lists the layers/checks that MUST fail, and
               optionally checks that MUST pass (to show which layer does the catching).
  * integrity -- tampering with the pinned upstream checkout, the pin, or the lakefile.
  * lint     -- unit tests for the source lint (stripping cannot hide banned tokens, etc.).

The Lean cases are copied into OpenProofs/Adversarial/ and OpenProofs/Statements/ for the run
and removed afterwards (both paths are gitignored for these files).

Usage: python3 tests/run_adversarial.py [--only lean|integrity|lint] [--case NAME]
Exit code 0 iff every expectation holds.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import check  # noqa: E402
import lint  # noqa: E402

ADV = ROOT / "tests" / "adversarial"
DEST = ROOT / "OpenProofs" / "Adversarial"
STMT = ROOT / "OpenProofs" / "Statements"
FIXTURES = ["AdvFixture.lean", "AdvFixtureBad.lean"]
LIB = ROOT / "OpenProofs" / "Lib"
LIB_FIXTURES = ["AdvLibGood.lean", "AdvLibBad.lean"]


def install() -> list[str]:
    DEST.mkdir(parents=True, exist_ok=True)
    STMT.mkdir(parents=True, exist_ok=True)
    mods = []
    for f in sorted((ADV / "cases").glob("*.lean")):
        shutil.copy(f, DEST / f.name)
        mods.append(f"OpenProofs.Adversarial.{f.stem}")
    for f in FIXTURES:
        shutil.copy(ADV / "fixtures" / f, STMT / f)
        mods.append(f"OpenProofs.Statements.{Path(f).stem}")
    LIB.mkdir(parents=True, exist_ok=True)
    for f in LIB_FIXTURES:
        shutil.copy(ADV / "fixtures" / "lib" / f, LIB / f)
        mods.append(f"OpenProofs.Lib.{Path(f).stem}")
    return mods


def uninstall(mods: list[str]) -> None:
    check.clean_outputs(ROOT, mods)
    shutil.rmtree(DEST, ignore_errors=True)
    for f in FIXTURES:
        (STMT / f).unlink(missing_ok=True)
    if STMT.exists() and not any(STMT.iterdir()):
        STMT.rmdir()
    for f in LIB_FIXTURES:
        (LIB / f).unlink(missing_ok=True)


def status(report: dict, name: str):
    for l in report["layers"]:
        if l["layer"] == name:
            return l["ok"]
        for c in l.get("checks", []) or []:
            if c["name"] == name:
                return c["ok"]
    return None


def run_lean(only_case: str | None) -> list[dict]:
    spec = json.loads((ADV / "cases.json").read_text())
    cases = [c for c in spec["cases"] if not only_case or only_case in (c["case"], c.get("label"))]
    mods = install()
    results = []
    try:
        check.clean_outputs(ROOT, mods)
        buildable = [m for m in mods if not m.endswith(".BrokenProof")]
        rc, out = check.run(["lake", "build", *buildable, "opcheck"], ROOT)
        if rc != 0:
            print("prebuild of adversarial modules failed:\n" + out[-3000:])
        for c in cases:
            claim = {
                "id": c.get("label", c["case"]),
                "module": f"OpenProofs.Adversarial.{c['case']}",
                "theorem": c["theorem"],
                "ref_kind": c["ref_kind"],
                "ref_module": c["ref_module"],
                "ref_theorem": c["ref_theorem"],
            }
            rep = check.check_claim(claim, ROOT, clean=False)
            problems = []
            for n in c.get("must_fail", []):
                s = status(rep, n)
                if s is not False:
                    problems.append(f"{n} expected FAIL, got {'PASS' if s else 'not run'}")
            for n in c.get("must_pass", []):
                s = status(rep, n)
                if s is not True:
                    problems.append(f"{n} expected PASS, got {'FAIL' if s is False else 'not run'}")
            if "identity" in c and rep.get("statement_identity") != c["identity"]:
                problems.append(f"statement identity {rep.get('statement_identity')} != expected {c['identity']}")
            if rep["verdict"] != c["verdict"]:
                problems.append(f"verdict {rep['verdict']} != expected {c['verdict']}")
            failed = [l["layer"] for l in rep["layers"] if not l["ok"]]
            failed_checks = [x["name"] for l in rep["layers"] for x in (l.get("checks") or []) if not x["ok"]]
            results.append({"group": "lean", "name": claim["id"], "ok": not problems,
                            "verdict": rep["verdict"], "failed_layers": failed,
                            "statement_identity": rep.get("statement_identity"),
                            "failed_checks": failed_checks, "axioms": rep.get("axioms"),
                            "problems": problems})
            print(f"{'ok ' if not problems else 'BAD'}  {claim['id']:<34} verdict={rep['verdict']:<4} "
                  f"identity={rep.get('statement_identity')} "
                  f"layers={failed} checks={failed_checks}" + (f"  !! {problems}" if problems else ""))
    finally:
        uninstall(mods)
    return results


def run_integrity() -> list[dict]:
    res = []

    def rec(name: str, ok: bool, detail="") -> None:
        res.append({"group": "integrity", "name": name, "ok": ok, "detail": detail})
        print(f"{'ok ' if ok else 'BAD'}  integrity/{name}  {detail if not ok else ''}")

    base = check.integrity(ROOT)
    rec("baseline_clean_passes", base["ok"], base["detail"])

    pkg = ROOT / ".lake" / "packages" / "formal_conjectures"
    target = pkg / "FormalConjectures" / "ErdosProblems" / "349.lean"
    original = target.read_bytes()
    try:
        target.write_bytes(original + b"\n-- tamper probe\n")
        r = check.integrity(ROOT)
        rec("tracked_upstream_edit_rejected", not r["ok"], r["detail"])
    finally:
        target.write_bytes(original)
        subprocess.run(["git", "-C", str(pkg), "checkout", "--", str(target.relative_to(pkg))])
    probe = pkg / "OpenProofsTamperProbe.lean"
    try:
        probe.write_text("theorem probe : True := trivial\n")
        r = check.integrity(ROOT)
        rec("untracked_upstream_file_rejected", not r["ok"], r["detail"])
    finally:
        probe.unlink(missing_ok=True)

    lf = (ROOT / "lakefile.toml").read_text()
    for extra in ['\nmoreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n', '\nplugins = ["x"]\n',
                  '\n[leanOptions]\ndebug.skipKernelTC = true\n']:
        rec(f"lakefile_rejects:{extra.strip()[:40]}", bool(check.lakefile_problems(lf + extra)))

    with tempfile.TemporaryDirectory() as td:
        t = Path(td)
        for f in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            shutil.copy(ROOT / f, t / f)
        up = json.loads((ROOT / "upstream.json").read_text())
        up["formal_conjectures"]["commit"] = "0" * 40
        (t / "upstream.json").write_text(json.dumps(up))
        r = check.integrity(t, pkgs_dir=ROOT / ".lake" / "packages")
        rec("pin_mismatch_rejected", not r["ok"], r["detail"])
        shutil.copy(ROOT / "upstream.json", t / "upstream.json")
        (t / "lakefile.lean").write_text("-- lean lakefile\n")
        r = check.integrity(t, pkgs_dir=ROOT / ".lake" / "packages")
        rec("lakefile_lean_rejected", not r["ok"], r["detail"])
        (t / "lakefile.lean").unlink()
        (t / "lean-toolchain").write_text("leanprover/lean4:v4.0.0\n")
        r = check.integrity(t, pkgs_dir=ROOT / ".lake" / "packages")
        rec("toolchain_mismatch_rejected", not r["ok"], r["detail"])
    return res


def run_lint() -> list[dict]:
    res = []

    def lint_text(text: str, role: str, name: str = "Probe.lean") -> list:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / name
            p.write_text(text)
            return lint.lint_file(p, role, Path(td))

    def rec(name: str, ok: bool) -> None:
        res.append({"group": "lint", "name": name, "ok": ok})
        print(f"{'ok ' if ok else 'BAD'}  lint/{name}")

    rec("char_literal_quote_cannot_hide_sorry",
        any(f.rule == "sorry" for f in lint_text("def c := '\"'\ntheorem t : True := by sorry\n", "result")))
    rec("comment_mention_of_sorry_flagged_raw",
        any("raw" in f.rule for f in lint_text("/- sorry -/\ntheorem t : True := trivial\n", "result")))
    rec("unterminated_string_cannot_hide_code",
        bool(lint_text('def s := "abc\ntheorem t : True := by native_decide\n', "result")))
    rec("nested_comment_close_handled",
        any(f.rule == "axiom declaration" for f in
            lint_text("/- /- -/ still comment -/\naxiom a : False\n", "result")))
    rec("csimp_flagged", any(f.rule == "csimp" for f in lint_text("attribute [csimp] foo\n", "result")))
    rec("lean_import_rejected",
        any("import not allowed" in f.rule for f in lint_text("import Lean.Elab.Command\n", "result")))
    rec("honest_result_clean",
        not lint_text("import Mathlib.Tactic\n/-! doc -/\nnamespace OpenProofs.X\n"
                      "theorem t : (2:ℕ) + 2 = 4 := by norm_num\nend OpenProofs.X\n", "result"))
    rec("statement_def_rejected",
        bool(lint_text("import Mathlib.Tactic\ndef f : ℕ := 1\ntheorem t : f = 1 := by sorry\n", "statement")))
    rec("statement_with_proof_rejected",
        bool(lint_text("import Mathlib.Tactic\ntheorem t : 1 = 1 := rfl\n", "statement")))
    rec("statement_clean",
        not lint_text("import Mathlib.Tactic\nnamespace OpenProofs.Statements.X\n"
                      "theorem t : (1 : ℕ) = 1 := by sorry\nend OpenProofs.Statements.X\n", "statement"))
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", choices=["lean", "integrity", "lint"])
    ap.add_argument("--case")
    args = ap.parse_args()
    results = []
    if args.only in (None, "lint"):
        results += run_lint()
    if args.only in (None, "integrity"):
        results += run_integrity()
    if args.only in (None, "lean"):
        results += run_lean(args.case)
    bad = [r for r in results if not r["ok"]]
    out = ROOT / "work" / "adversarial-last-run.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(results, indent=1, ensure_ascii=False))
    print(f"\n{len(results) - len(bad)}/{len(results)} expectations hold" + (f"; FAILURES: {[r['name'] for r in bad]}" if bad else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
