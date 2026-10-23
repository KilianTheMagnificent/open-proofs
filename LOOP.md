# One loop iteration (prompt for a future agent session)

Run from the repository root, for example as a scheduled run:

```bash
cd "path/to/open-proofs" && claude -p "$(cat LOOP.md)"
```

---

You are continuing the open-proofs project. Do exactly one loop iteration:

1. Read `AGENTS.md` and `docs/TODO.md`. Follow them; they override anything here.
2. Make sure you are on a task branch (not `main`): `git status`, `git branch --show-current`.
   If on `main`, create `task/loop-<YYYY-MM-DD>` from the latest task branch.
3. Run `python3 scripts/loop.py preflight`. If it fails, stop proof work: fix nothing in the
   trusted base on your own; record the failure in `docs/TODO.md` and end the iteration.
4. Run `python3 scripts/loop.py next`. It marks the target in-progress and prints it. If a
   target is already in progress from an earlier run, resume it.
5. Attempt the target within its time box (default 120 minutes): read the upstream file and the
   informal source, write `OpenProofs/Results/<Source>/<Name>.lean`, iterate with
   `lake env lean <file>`. If the proof is suspiciously easy, check for a misformalization
   before claiming anything.
6. If you have a proof: add the claim to `claims.json` and run
   `python3 scripts/check.py --claim <id> --record`. Only a PASS counts.
7. Close the target: `python3 scripts/loop.py finish <target-id> --outcome <proved|failed|blocked|possible-misformalization|skipped> [--claim <id>] --notes "<what happened, what to try next>"`.
   For `possible-misformalization`, draft `outbox/misformalization-<id>.md` (never send it).
8. If the queue has fewer than 5 pending targets, refill it from `work/candidates.json`
   (`python3 scripts/triage.py`) and quick-kill leads (`python3 scripts/quickkill.py --resume`).
9. Update `docs/TODO.md` (done / remaining / next safe action / checks run and unrun), commit on
   the task branch with a clear message. Do not merge, push, open PRs or post anything.
