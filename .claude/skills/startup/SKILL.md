---
name: startup
description: Start or resume the open-proofs proving loop with parallel prover subagents. Use when the user says "startup", "go", "start", "start proving" or "resume" in the open-proofs project. Optional arguments like "provers=3 budget=5 model=sonnet mode=subagents|sequential|swarm".
---

# startup: run the open-proofs loop (Claude Code accelerator)

This skill is an accelerator for AGENTS.md "Startup". It must not ask the user anything. If any
step below is impossible in this session, fall back to the sequential loop in AGENTS.md.

## 0. Parameters

Parse the user's message for `provers=N`, `budget=K` (targets to attempt, 0 = until the queue
is empty), `model=M`, `mode=subagents|sequential|swarm`. Defaults come from `./op config`:

```bash
./op config --get provers         # default 3
./op config --get budget_targets  # default 0 (unlimited)
./op config --get prover_model    # default empty = inherit this session's model
```

Default mode: `subagents`. A `prover_model` value is passed to the Agent tool's `model`
parameter only if it is one of the aliases that tool accepts (for example `sonnet`, `opus`,
`haiku`); otherwise omit `model` (the prover inherits this session's model), or use
`mode=swarm`, which passes any model id to the configured CLI.

## 1. Preflight (stop on failure)

```bash
./op status
./op preflight
./op branch            # moves off main onto task/loop-<date> if needed
```

If preflight fails: do not prove anything; add a dated line to `docs/TODO.md` with the failure
and stop. If `./op status` shows fewer than `2 × provers` pending targets, run `./op refill`.

## 2. Loop (mode=subagents)

Repeat until the budget is spent, `./op begin`-style claims report an empty queue, or
`work/STOP` exists (`./op status` prints "STOP requested"):

1. Claim one target per free prover slot, using distinct agent names:
   `./op next --agent prover-<k> --json`. The output is JSON with `target.id`. Exit code 3 means
   the queue is empty for now (run `./op refill` once; if still empty, finish).
2. Spawn one `prover` subagent per claimed target **in a single message** (parallel; foreground,
   so the turn waits for all of them). Prompt for each:
   `Target: <id>. Agent name: prover-<k>. Follow your instructions (AGENTS.md "Prover procedure").`
   Add `model` only as described in section 0.
3. When they return, run `./op status`. For any of your targets still `in-progress`, run
   `./op giveup '<id>' --notes 'prover returned without finishing: <its last report line>'`.
4. `./op commit -m "Loop: <ids and outcomes>"` (provers already commit on done/giveup; this
   catches anything left).
5. Count attempted targets against the budget; continue with step 1.

## 2'. Other modes

- `mode=sequential`: do the AGENTS.md "Sequential loop" yourself, one target at a time.
- `mode=swarm`: run `./op swarm --provers N [--budget K] [--model M] [--cli claude|codex]` in the
  background and report its log (`work/swarm/`). It launches headless workers of the configured
  agent CLI (`op.config.json`).

## 3. Wrap up (always)

```bash
./op status
```

Append a dated summary to `docs/TODO.md` (targets attempted, PASS results, give-ups with
reasons, anything blocking), then `./op commit -m "Loop summary <date>"`. Never push, never
open PRs or issues, never post anything. Report: targets attempted, PASS results, the branch.
