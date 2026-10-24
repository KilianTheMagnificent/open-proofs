#!/usr/bin/env python3
"""End-to-end check of the turnkey entry point: run a real headless agent session on "startup".

  python3 tests/e2e_startup.py claude --max-turns 60 --prompt "startup provers=2 budget=2"
  python3 tests/e2e_startup.py codex --minutes 25 --prompt "startup budget=1"

Records the session transcript under work/e2e/, then reports: duration, tool calls, permission
denials or approval requests, questions asked, queue/claim changes, and new checker verdicts.
Exit code 0 iff the session ran with no permission denials and no questions.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "work" / "e2e"


def snapshot() -> dict:
    q = json.loads((ROOT / "ledger" / "queue.json").read_text())
    res = json.loads((ROOT / "ledger" / "results.json").read_text())["results"]
    status = {t["id"]: t["status"] for t in q["targets"]}
    verdicts = {k: (v["check"]["verdict"], v["check"]["checked_at"]) for k, v in res.items()}
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    return {"status": status, "verdicts": verdicts, "head": head}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("cli", choices=["claude", "codex"])
    ap.add_argument("--prompt", default="startup")
    ap.add_argument("--max-turns", type=int, default=60)
    ap.add_argument("--minutes", type=int, default=90, help="wall-clock cap")
    ap.add_argument("--model", default="")
    args = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    log = OUT / f"{args.cli}-{stamp}.jsonl"
    if args.cli == "claude":
        cmd = ["claude", "-p", args.prompt, "--max-turns", str(args.max_turns), "--output-format",
               "stream-json", "--verbose"] + (["--model", args.model] if args.model else [])
    else:
        cmd = ["codex", "exec", "-C", str(ROOT), "-s", "workspace-write", "--json"] + \
              (["-m", args.model] if args.model else []) + [args.prompt]
    before = snapshot()
    t0 = time.time()
    with log.open("w") as fh:
        try:
            p = subprocess.run(cmd, cwd=ROOT, stdout=fh, stderr=subprocess.STDOUT, timeout=args.minutes * 60)
            rc, timed_out = p.returncode, False
        except subprocess.TimeoutExpired:
            rc, timed_out = None, True
    secs = time.time() - t0
    after = snapshot()
    events = []
    for line in log.read_text().splitlines():
        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    text = log.read_text()
    tool_calls, denials, questions, mcp = 0, [], 0, None
    for e in events:
        if e.get("type") == "system" and e.get("subtype") == "init":
            mcp = e.get("mcp_servers")
        if e.get("type") == "assistant":
            for c in (e.get("message", {}).get("content") or []):
                if c.get("type") == "tool_use":
                    tool_calls += 1
                    if c.get("name") == "AskUserQuestion":
                        questions += 1
        if e.get("type") == "result":
            denials += e.get("permission_denials") or []
        if args.cli == "codex":
            item = e.get("item") or {}
            if item.get("type") in ("command_execution", "mcp_tool_call", "file_change"):
                tool_calls += 1
    if args.cli == "codex":
        for kw in ("approval required", "rejected by user", "sandbox denied", "Operation not permitted"):
            if kw in text:
                denials.append(kw)
    changed = {k: (before["status"].get(k), v) for k, v in after["status"].items() if before["status"].get(k) != v}
    new_verdicts = {k: v for k, v in after["verdicts"].items() if before["verdicts"].get(k) != v}
    commits = subprocess.run(["git", "log", "--oneline", f"{before['head']}..HEAD"], cwd=ROOT,
                             capture_output=True, text=True).stdout.strip().splitlines()
    report = {"cli": args.cli, "prompt": args.prompt, "exit_code": rc, "timed_out": timed_out,
              "seconds": round(secs), "tool_calls": tool_calls, "permission_denials": denials,
              "questions_asked": questions, "mcp_servers": mcp, "queue_changes": changed,
              "new_verdicts": new_verdicts, "new_commits": commits, "log": str(log.relative_to(ROOT))}
    (OUT / f"{args.cli}-{stamp}.report.json").write_text(json.dumps(report, indent=1, ensure_ascii=False))
    print(json.dumps(report, indent=1, ensure_ascii=False))
    return 0 if not denials and not questions else 1


if __name__ == "__main__":
    sys.exit(main())
