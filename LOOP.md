# Scheduled loop run (prompt for a headless agent session)

Any agent CLI that reads AGENTS.md works. Examples (run from the repository root):

```bash
claude -p "startup budget=3" --max-turns 200          # Claude Code: startup skill, parallel provers
codex exec -C "$PWD" -s workspace-write "startup"      # Codex: AGENTS.md sequential loop
```

---

startup

Follow AGENTS.md "Startup" exactly. Do not ask questions. If the owner gave a budget in this
prompt, stop after that many targets; otherwise run until the queue is empty or `work/STOP`
exists. Finish with the dated summary in `docs/TODO.md` and `./op commit`.
