# TODO

Updated 2026-10-24 (end of iteration 2, "turnkey"). Branch `task/turnkey` (from
`task/first-iteration`; nothing merged into `main`, nothing pushed). Agent memory for this
project = `AGENTS.md` + this file.

## Done

### Iteration 1 (branch `task/first-iteration`)

- Setup: elan 4.2.4; Lean v4.33.1 installed by hand from the GitHub release asset (sha256
  checked; `release.lean-lang.org` is blocked by a Cisco Umbrella filter); Lake project pinned to
  formal-conjectures `96343eeb` (Mathlib `0df444a3`); Mathlib cache; all Erdős modules built.
- Checker: `scripts/check.py` + `OpenProofsChecker/Main.lean` + `scripts/lint.py`, five layers.
- Triage tools, quick-kill sweep, placeholder-dependency scan, status cross-check.
- 35 claims: 22 tier-a proofs, 2 tier-b special cases, 11 possible misformalizations; drafts in
  `outbox/`.

### Iteration 2 (turnkey; branch `task/turnkey`)

- **Entry points:** `AGENTS.md` "Startup" is the universal entry for any agent CLI and model
  (Sequential loop + Prover procedure, all through `./op`); `CLAUDE.md` = `@AGENTS.md`;
  `.claude/skills/startup` (parallel `prover` subagents); `.claude/agents/prover.md`;
  `LOOP.md` for scheduled headless runs.
- **Session plumbing:** `.claude/settings.json` (env with elan PATH and Lean caps; allowlist for
  `./op`, `lake build/env`, `lean`, project scripts, read-only shell, git add/commit/branch/
  switch, `mcp__lean-lsp`; denies for push, `gh`, `curl`/`wget`/`ssh`, `lake update/clean`,
  posting connectors, Artifact tools, and all tooling/trusted-base edits; `enabledMcpjsonServers`;
  SessionStart hook `op status --brief`, measured 0.06 s).
- **`./op` CLI** (`scripts/op.py`): status, next (lock files, stale-claim expiry), begin,
  scaffold (exact upstream statement incl. opens/variables/`open … in`, verified by a
  `type_of%` identity check), try (JSON messages, goal states, lint preview, crash detection,
  caps), search (250k-declaration local index; `exact?`/`apply?`/… harness), check, done,
  giveup (saves work to `work/attempts/`, requeues once), finish, notes (`ledger/notes/`),
  refill, build, commit, branch, stop, config, swarm (headless workers of any configured CLI),
  preflight, recheck. `scripts/loop.py` is now a shim.
- **Resource caps:** `LEAN_NUM_THREADS=2` (Lake honours it: measured 2 concurrent lean
  processes), `lean -j2 -M8192` for `try`, ≤4 concurrent `try`, one global build lock, wall-clock
  timeouts. Peak RSS seen in a run: ~6.9 GB.
- **Lean LSP MCP:** `lean-lsp-mcp` 0.31.0 via `uv tool` in `.mcp.json` (remote search tools
  disabled); goal and diagnostics calls verified with v4.33.1 by `tests/mcp_smoke.py`
  (MCP SMOKE OK); connected in the headless Claude Code runs.
- **Configurable provers:** `op.config.json` + `OP_*` env (CLI `claude`/`codex`, model default
  empty = CLI default; no hardcoded model ids).
- **Queue:** `./op refill` scored every formal-conjectures directory: 4118 pending → now 4114
  (tier a: d1 35, d2 79, d3 1369, d4 1204, d5 60; tier c: 1371), one target per line.
- **Shared helpers:** `OpenProofs/Lib/{Graph,Padic}.lean`; adversarial cases `LibGoodUse`,
  `LibSorryUse`, `LibSorryUnused` (suite now 48/48).
- **End-to-end runs (all headless, real config):**
  - `claude -p "startup provers=2 budget=2" --max-turns 60`: 636 s, 2 targets proved (PASS):
    `Arxiv.«2604.08040».cyc_alternatingGroup_five`, `Arxiv.«1609.08688».maximalLength_four`;
    0 questions; 1 permission denial (the orchestrator tried to patch `scripts/op.py`; that path
    was "ask", now "deny"; the underlying `op try` crash-reporting bug is fixed).
  - `codex exec -s workspace-write "startup budget=1"`: 193 s, proved
    `BrennanConjecture.integralMeansSpectrum_id` (PASS); the sandbox blocked the first git commit
    (`op commit` now fails softly; `op done` reports it honestly), a later commit succeeded.
  - `claude -p "startup provers=1 budget=1" --max-turns 40` after the fixes: 263 s, 0 denials,
    0 questions, proved `Erdos1074.erdos_1074.variants.EHSNumbers_init` (PASS).
  - `./op swarm --provers 1 --budget 1 --cli claude` (live): 140 s, worker proved
    `Erdos1074.erdos_1074.variants.PillaiPrimes_init` (PASS) and committed.
  - All Claude Code runs printed "Ignoring 51 permissions.allow entries … workspace has not been
    trusted": `open-proofs/` itself is not yet trusted, so the runs went through the owner's
    `auto` permission mode, not the project allowlist (deny rules still applied).
- Ledger: 40 claims, 40 PASS under the current trusted base.

## Remaining

- Keep running the loop (`startup`); 4114 targets pending. Tier-c targets are only time-boxed.
- Difficulty estimates are heuristic (e.g. `Erdos633.IsCuttable.sq` was rated 1 but is a
  geometric dissection); provers should give up early and say why in notes.
- Erdős 506 (conditional), 409.parts.iii, 975.variants.quadratic: suspected issues without Lean
  proof. Re-verifying external `formal_proof` links; sweeps beyond `ErdosProblems`;
  `leanchecker --fresh` deep replay: all still unrun.
- Owner, one time: accept Claude Code's folder-trust dialog in `open-proofs/` (or set
  `hasTrustDialogAccepted` for it in `~/.claude.json`) so the project allowlist takes effect;
  until then interactive sessions outside `auto` mode may prompt.
- Owner decisions: publish the repo (needed for any `formal_proof` URL), send any outbox draft,
  merge `task/turnkey` into `main`. Tooling changes need an owner-approved maintenance session
  (loop sessions are denied tooling edits).

## Next safe action

Open a CLI session in `open-proofs/` and say `startup` (Claude Code: parallel provers; any
other CLI: sequential loop). For an unattended run: `./op swarm --provers 3`.

## Checks (iteration 2)

- Passed: `tests/run_adversarial.py` 48/48; `./op recheck` 35/35 then 4 new PASS (39/39 under the
  current trusted base); `tests/mcp_smoke.py` OK; `./op preflight` OK; SessionStart hook 0.06 s;
  `./op try` 4.4 s (11.7 s with `--goals`) against a 300 s cap; three headless startup runs above.
- Not run: live `op swarm`; `leanchecker --fresh`; any upstream submission (out of scope).

## Loop log

### Loop summary 2026-10-23 (startup provers=2 budget=2, branch task/turnkey)

- Preflight OK. Attempted 2 targets, 2 PASS (identity syntactic; axioms propext, Classical.choice, Quot.sound):
  `Arxiv.«2604.08040».cyc_alternatingGroup_five` (32 cyclic subgroups of A5; kernel `decide`) and
  `Arxiv.«1609.08688».maximalLength_four` (F(4)=8; explicit witness plus a recursor-based DFS checked
  by `decide +kernel` in 7 chunks; peak RSS ~6.9 GB under `-M8192`).
- Bug (FIXED in the turnkey iteration: `run_lean` now reports a nonzero exit without messages as an
  error; verified with a forced `memory_exception`): `./op try` printed `== OK` when Lean crashed without an error message (e.g.
  `lean::memory_exception` under `-M`). `run_lean` in `scripts/op.py` ignores the exit code. Fix: when
  the exit code is nonzero and there is no error message, add a synthetic error. Not in the trusted base;
  the edit was not permitted in this session. Until it is fixed, confirm a kernel-heavy OK with
  `lake env lean <file>` and check its exit status. `./op done` (the full checker) is unaffected.
- Kernel-computation tip: write the search helpers with `List.rec`/`Nat.rec`. The pattern-matching
  versions ran out of kernel memory under `-M8192`.

### Loop summary 2026-10-24 (startup budget=1, branch task/turnkey)

- Budget exhausted: attempted one target, proved `BrennanConjecture.integralMeansSpectrum_id`.
  The identity has derivative one, making the numerator constant; the absolute logarithm in
  the denominator tends to infinity as the radius approaches one from below.
  Proof: `OpenProofs/Results/Wikipedia/Brennanconjecture_integralMeansSpectrum_id.lean`.
- Checks: `./op preflight` OK (10/10 lint and 9/9 integrity expectations);
  `./op try ... --goals` OK with zero errors and warnings; `./op done` PASS on all five layers,
  syntactic statement identity, only `propext`, `Classical.choice`, `Quot.sound`.
  Ledger now has 38/38 PASS, 4115 pending targets, and no active claim.
  Full adversarial suite and deep replay were not rerun; no tooling or trusted-base edits.
- Tooling follow-up (FIXED in 254e153): `cmd_done` ignored `cmd_commit`'s return code and prints "recorded and
  committed" even when sandboxed Git cannot create `.git/index.lock`. Observed here on
  `9aa0625`; the proof and ledger were recorded correctly. Proposed maintenance fix: retain
  the commit return code and report "recorded; commit pending" on failure. No tooling edits
  made during this loop.
- Next safe action: `startup` for the next budgeted loop; next queued target is
  `Erdos1074.erdos_1074.variants.EHSNumbers_init`. No merge, push, or upstream submission.

### Loop summary 2026-10-24 (Claude Code, provers=1 budget=1)

- Preflight OK (10/10 lint, 9/9 integrity). Branch `task/turnkey`.
- Attempted 1 target: `Erdos1074.erdos_1074.variants.EHSNumbers_init` (tier a, test) —
  proved, checker PASS on all five layers, axioms `propext`, `Classical.choice`, `Quot.sound`
  (commit `45c7e73`). Proof by computation for m ≤ 17: prime witnesses p | m!+1 with
  p ≢ 1 (mod m) for members, full factorizations of m!+1 for non-members, then
  `Nat.count`/`Nat.nth_count`. No misformalization signs.
- Ledger: 39/39 PASS, 4114 pending. No give-ups, nothing blocking; no tooling edits.
- Next queued: `Erdos1074.erdos_1074.variants.PillaiPrimes_init`. No merge, push or submission.

### Swarm run 2026-10-24 00:12–03:25 (`./op swarm --provers 3`, Claude Code default model, branch `task/run-2026-10-24`)
- 114 targets attempted: 102 proved, 12 blocked (Poincaré variants ×5, RegularPrimes ×3, MovingSofa, Erdős 69, Erdős 707 small_sidon_sets, AgohGiuga 13000 digits). All tier a; upstream categories of the proved ones: textbook 61, test 28, API 10, research solved 3. No tier b/c target reached; no new misformalization drafts.
- Verified after the run: `scripts/check.py --all` 142/142 PASS (axioms exactly propext/Classical.choice/Quot.sound; identity 140 syntactic, 2 kernel-defeq); `tests/run_adversarial.py` 48/48.
- Next safe action: to reach open problems, give one prover tier b/c targets (the queue is ordered easiest-first, 3,999 pending), or run `./op refill` with tier c prioritised. Branch not merged.

### Publishing (2026-10-24)
- Done: all task branches fast-forwarded into `main`. History rewritten to the owner's GitHub noreply identity with local paths scrubbed (`.mcp.json` uses `${HOME}`; the machine `PATH` lives in the gitignored `.claude/settings.local.json`). Added README and Apache-2.0 LICENSE. Repo-local git identity is now the noreply address.
- Blocked: Claude Code's auto-mode permission check denied creating the public repo (`gh repo create`), so the owner has to run it. Nothing is published or filed yet.
- Ready: `outbox/issue-value-answers-ignore-parameter.md` is one consolidated upstream issue covering 142 (two statements), 319, 321, 361, 409.variants.sigma, 503 and 692.parts.ii. Excluded because they're already reported upstream: 409.parts.i (#7434), 450 and 552 (#7493, PR #7495). Excluded because it has no Lean evidence: 506. Its links point at commit `a1fc786` in KilianTheMagnificent/open-proofs.
- Next safe action (owner): `gh repo create KilianTheMagnificent/open-proofs --public --source . --remote origin && git push -u origin main`, then `gh issue create --repo google-deepmind/formal-conjectures --title "…" --body-file outbox/issue-value-answers-ignore-parameter.md`.
