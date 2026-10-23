#!/usr/bin/env python3
"""Resumable work loop for open-proofs: queue management plus the deterministic loop steps.

The creative step (writing a proof) is done by an agent session following LOOP.md. This script
does everything around it:

  python3 scripts/loop.py preflight          integrity + lint/integrity adversarial tests
                                             (add --full to also run the Lean adversarial cases)
  python3 scripts/loop.py next               pick the next target, mark it in-progress, print a brief
  python3 scripts/loop.py status             queue summary
  python3 scripts/loop.py finish ID --outcome OUTCOME [--claim CLAIM_ID] --notes "..."
                                             record an attempt; OUTCOME is one of
                                             proved | failed | blocked | possible-misformalization | skipped
  python3 scripts/loop.py recheck            re-run the checker on every claim and record verdicts

`finish --outcome proved` requires --claim and refuses unless ledger/results.json holds a PASS
for that claim, checked against the current trusted base. The queue never records a proof
that the checker has not passed.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUEUE = ROOT / "ledger" / "queue.json"
RESULTS = ROOT / "ledger" / "results.json"
sys.path.insert(0, str(ROOT / "scripts"))
OUTCOMES = ["proved", "failed", "blocked", "possible-misformalization", "skipped"]
TIER_ORDER = {"a": 0, "b": 1, "c": 2}


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def load() -> dict:
    return json.loads(QUEUE.read_text())


def save(q: dict) -> None:
    q["updated"] = now()
    QUEUE.write_text(json.dumps(q, indent=1, ensure_ascii=False) + "\n")


def sort_key(t: dict):
    return (TIER_ORDER.get(t.get("tier", "c"), 9), t.get("priority", 100), t["id"])


def cmd_status(_args) -> int:
    q = load()
    counts: dict[str, int] = {}
    for t in q["targets"]:
        counts[t["status"]] = counts.get(t["status"], 0) + 1
    print(f"queue updated {q.get('updated')}: {counts}")
    for t in sorted(q["targets"], key=sort_key):
        print(f"  [{t['status']:<26}] tier {t['tier']} p{t.get('priority', 100):<3} {t['id']}")
    return 0


def cmd_next(args) -> int:
    q = load()
    stale = [t for t in q["targets"] if t["status"] == "in-progress"]
    if stale and not args.ignore_in_progress:
        t = stale[0]
        print(f"NOTE: {t['id']} is still marked in-progress (started {t['attempts'][-1]['started'] if t.get('attempts') else '?'}).")
        print("Resume it, or close it with `loop.py finish`. Showing it as the current target.\n")
    else:
        pending = sorted([t for t in q["targets"] if t["status"] == "pending"], key=sort_key)
        if not pending:
            print("queue empty: run scripts/triage.py and scripts/quickkill.py, then add targets (see AGENTS.md)")
            return 1
        t = pending[0]
        t["status"] = "in-progress"
        t.setdefault("attempts", []).append({"started": now(), "outcome": None, "notes": ""})
        save(q)
    print(json.dumps(t, indent=1, ensure_ascii=False))
    stem = t["ref_theorem"].replace(".", "_")
    print(f"\nSuggested result file: OpenProofs/Results/<Source>/<Short>.lean  (e.g. derived from {stem})")
    print(f"Timebox: {t.get('timebox_minutes', 120)} minutes. Then: add a claim to claims.json, run\n"
          f"  python3 scripts/check.py --claim <claim-id> --record\n"
          f"and close with\n  python3 scripts/loop.py finish {t['id']} --outcome <...> [--claim <claim-id>] --notes '...'")
    return 0


def cmd_finish(args) -> int:
    q = load()
    t = next((x for x in q["targets"] if x["id"] == args.id), None)
    if t is None:
        print(f"no target {args.id!r}", file=sys.stderr)
        return 2
    if args.outcome == "proved":
        if not args.claim:
            print("--outcome proved needs --claim", file=sys.stderr)
            return 2
        import check  # noqa: E402

        res = json.loads(RESULTS.read_text())["results"].get(args.claim) if RESULTS.exists() else None
        if not res or res["check"]["verdict"] != "PASS":
            print(f"refusing: no PASS verdict for claim {args.claim!r} in ledger/results.json", file=sys.stderr)
            return 3
        if res["check"]["trusted_base_sha256"] != check.trusted_base_hash(check.ROOT):
            print("refusing: the recorded PASS predates a trusted-base change; re-run scripts/check.py --record",
                  file=sys.stderr)
            return 3
    if not t.get("attempts") or t["attempts"][-1].get("outcome") is not None:
        t.setdefault("attempts", []).append({"started": None})
    t["attempts"][-1].update({"finished": now(), "outcome": args.outcome, "notes": args.notes or "",
                              "claim": args.claim})
    t["status"] = {"failed": "pending" if args.retry else "failed"}.get(args.outcome, args.outcome)
    save(q)
    print(f"{t['id']}: {t['status']}")
    return 0


def run(cmd: list[str]) -> int:
    print("$ " + " ".join(cmd), flush=True)
    return subprocess.call(cmd, cwd=ROOT)


def cmd_preflight(args) -> int:
    rc = run([sys.executable, "scripts/check.py", "--integrity"])
    rc |= run([sys.executable, "tests/run_adversarial.py", "--only", "lint"])
    rc |= run([sys.executable, "tests/run_adversarial.py", "--only", "integrity"])
    if args.full:
        rc |= run([sys.executable, "tests/run_adversarial.py", "--only", "lean"])
    print("PREFLIGHT " + ("OK" if rc == 0 else "FAILED: do not trust the checker until this is fixed"))
    return rc


def cmd_recheck(_args) -> int:
    return run([sys.executable, "scripts/check.py", "--all", "--record"])


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status")
    p = sub.add_parser("next")
    p.add_argument("--ignore-in-progress", action="store_true")
    p = sub.add_parser("finish")
    p.add_argument("id")
    p.add_argument("--outcome", required=True, choices=OUTCOMES)
    p.add_argument("--claim")
    p.add_argument("--notes")
    p.add_argument("--retry", action="store_true", help="for failed: put the target back to pending")
    p = sub.add_parser("preflight")
    p.add_argument("--full", action="store_true")
    sub.add_parser("recheck")
    args = ap.parse_args()
    return {"status": cmd_status, "next": cmd_next, "finish": cmd_finish, "preflight": cmd_preflight,
            "recheck": cmd_recheck}[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
