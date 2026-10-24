# open-proofs: agent instructions

This file and `docs/TODO.md` are the project's only agent memory. They are written for every
agent CLI and every model: Claude Code (any model), Codex, and any other tool that reads
`AGENTS.md`. Claude-only features (the `startup` skill, prover subagents, hooks, the Lean MCP
server) only speed things up; nothing here requires them. Parent rules:
`~/Developer/Projects/AGENTS.md` (this file overrides them where they differ).

## Startup (when the owner says "startup", "go", "start" or "resume")

Do not ask questions. Run these commands from the repository root, in order:

1. `./op status` — branch, queue, claims in progress, recent results.
2. `./op preflight` — checker self-tests. If it prints `PREFLIGHT FAILED`, stop: add a dated
   line about it to `docs/TODO.md`, run `./op commit -m "Preflight failed"` and report.
3. `./op branch` — moves you off `main` onto `task/loop-<date>` if needed.
4. If `./op status` shows fewer than 10 pending targets: `./op refill`.
5. Run the loop:
   - **Claude Code:** use the `startup` skill (`.claude/skills/startup/SKILL.md`): parallel
     `prover` subagents. If anything in it is unavailable, use the sequential loop below.
   - **Any other agent CLI or model:** the **Sequential loop** below.
   - **Unattended, any CLI:** `./op swarm` (see "Parallel provers").
6. Stop when the queue is empty, a budget the owner gave you is spent, or `work/STOP` exists
   (`./op stop` creates it). Then append a dated summary to `docs/TODO.md` and run
   `./op commit -m "Loop summary <date>"`.

### Sequential loop (works with any agent and any model)

Repeat:

1. `./op begin --agent <your-name>` → prints a WORK ORDER: `TARGET`, `EDIT` (the file to
   edit), `UPSTREAM FILE`, earlier notes, the time box. Exit code 3 = queue empty: stop.
   Exit code 4 = stop requested: stop.
2. Do the **Prover procedure** for that target.
3. Go back to 1.

### Prover procedure (one target)

1. Read the `UPSTREAM FILE` around the target (docstring = informal statement) and the earlier
   notes printed by `./op begin` (`./op notes '<TARGET>'`). Do not repeat recorded dead ends.
2. Open the `EDIT` file. Keep the theorem statement exactly as scaffolded. Replace the
   placeholder after `:= by` with a proof. Helper lemmas go above the theorem with distinctive
   names (never an upstream name), or in `OpenProofs/Lib/` if reusable.
3. After every change: `./op try <EDIT file> --goals`. It prints errors and the goal state at
   each remaining placeholder, then a line `== OK…`, `== FAIL…` or `== TIMEOUT…`, plus any
   lint findings the checker would reject.
4. Find lemmas: `./op search name <regex>`, `./op search type <regex>`,
   `./op search exact '<goal>' --ctx '<binders>' [--tactic 'apply?']`.
5. When `./op try` prints `== OK:` with 0 errors and no placeholder warning:
   `./op done '<TARGET>'`. It runs the full checker; on PASS it records, closes the target and
   commits (`== DONE`). On `== FAIL` fix the reported layer and run it again.
6. Time box over or stuck: `./op giveup '<TARGET>' --notes '<what you tried; dead ends; next idea>'`.
   Your file is saved to `work/attempts/` and restored for the next attempt.
7. Statement looks false or trivially true for a formalization reason (vacuous hypothesis,
   `sSup`/`sInf` of an empty or unbounded set, a placeholder answer that cannot depend on a
   quantified parameter, natural subtraction, …): compare with the informal statement; then
   `./op giveup '<TARGET>' --outcome possible-misformalization --notes '<why>'` and draft
   `outbox/misformalization-<target>.md`. A proof of the negation or of an answer-free variant
   goes through `OpenProofs/Statements/` (see "Variants").
8. Working longer than 20 minutes without `./op try`? Run `./op heartbeat '<TARGET>'`
   (claims expire after `OP_LOCK_TTL_HOURS`, default 3 h, without a heartbeat).

**Never** write these words in a result file, even in comments: `sorry`, `admit`,
`native_decide`, `implemented_by`, `skipKernelTC`, `ofReduceBool`, `trustCompiler`, `run_cmd`,
`run_tac`, `#eval`, `addDecl`. No `axiom`, `opaque`, `unsafe`, `partial`, `extern`, `macro`,
`syntax`, `elab`, `notation`, `set_option debug.*`. Kernel `decide` is fine.

### Parallel provers (accelerators)

- **Claude Code:** the `startup` skill claims N targets (`./op next --agent prover-k --json`)
  and runs N `prover` subagents (`.claude/agents/prover.md`) in parallel, then commits and repeats.
- **Any CLI:** `./op swarm [--provers N] [--cli claude|codex] [--model M] [--budget K]` claims
  targets and launches headless workers of the configured agent CLI, each running the Prover
  procedure for one target. Logs: `work/swarm/`. Stop with `./op stop`.
- **Configuration** (`op.config.json`, overridden by environment): `provers` (`OP_PROVERS`,
  default 3), `prover_cli` (`OP_PROVER_CLI`, default `claude`), `prover_model`
  (`OP_PROVER_MODEL`, default empty = the CLI's own default; no model id is hardcoded),
  `max_turns`, `budget_targets` (`OP_BUDGET`, 0 = unlimited), `worker_timeout_minutes`, and the
  command template per CLI. `./op config` prints the effective values.

### Resource caps (parallel runs must not freeze the Mac)

`op` sets `LEAN_NUM_THREADS` (Lake's job pool and Lean's threads) to `OP_LEAN_THREADS` (2),
passes `lean -j2 -M8192` to every `./op try`, allows at most `OP_MAX_TRIES` (4) concurrent
`try` processes, and serializes all `lake build`/checker runs through one global build lock
(`work/locks/build`), with `OP_TRY_TIMEOUT` (300 s) and `OP_BUILD_TIMEOUT` (3600 s) wall-clock
limits. The Claude Code settings and the MCP server set `LEAN_NUM_THREADS=2` too.

## `op` reference

| Command | What it does |
|---|---|
| `./op status [--brief]` | Queue counts, claims in progress, next targets, recent results (`--brief`: SessionStart hook, ~0.1 s, no builds) |
| `./op begin [--target T] [--agent A] [--tier a] [--max-difficulty N] [--dir D] [--fresh]` | Claim (or resume) a target, scaffold it, print the work order |
| `./op next [--agent A] [--json]` | Claim only (lock file in `work/locks/targets/`; stale claims expire) |
| `./op scaffold T [--force] [--fresh]` | Write `OpenProofs/Results/<Dir>/<File>_<thm>.lean` with the exact upstream statement, opens, variables and namespace; verify it elaborates to the upstream type |
| `./op try FILE [--goals] [--timeout S] [--json]` | Compile one file with caps; errors, warnings, goals; lint preview; also a heartbeat |
| `./op search name\|type REGEX` | Local index of Mathlib, formal-conjectures and OpenProofs declarations |
| `./op search exact GOAL [--ctx C] [--import M] [--tactic T]` | Run `exact?` (or `apply?`, `rw?`, `simp?`, `aesop?`, `hint`) on a goal |
| `./op done T` | Create the claim if needed, run the full checker, record, close as proved, commit |
| `./op giveup T --notes N [--outcome failed\|blocked\|skipped\|possible-misformalization]` | Save the work to `work/attempts/`, close or requeue (first failure requeues at lower priority), commit |
| `./op check T\|CLAIM`, `./op finish T --outcome O --notes N` | Lower-level pieces of `done`/`giveup` |
| `./op notes T [--add TEXT]` | Per-target attempt log in `ledger/notes/` (committed) |
| `./op refill [--dirs all\|D1,D2] [--dry-run]` | Add scored targets from every formal-conjectures directory |
| `./op build MODULE…` | `lake build` under the build lock with caps |
| `./op commit -m MSG` | Commit ledger, claims, notes, outbox, docs and every result with a PASS |
| `./op branch`, `./op stop [--clear]`, `./op config [--get K]`, `./op swarm …` | Session plumbing |
| `./op preflight [--full]`, `./op recheck` | Checker self-tests; re-check every claim |

The Lean LSP MCP server (`.mcp.json`, `lean-lsp-mcp` 0.31.0) adds goal-state, diagnostics,
hover and multi-attempt tools in Claude Code (`mcp__lean-lsp__*`); `tests/mcp_smoke.py`
verifies it. Network-backed search tools of that server are disabled.

## Purpose

A recurring, bottomless token sink with a perfect external oracle: machine-checked Lean 4 proofs
of statements from google-deepmind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(Erdős problems and similar) whose upstream proof is still a placeholder. Nobody reviews the
output by hand. **The checker is the review**, so its integrity matters more than any result.

Tiers: **(a)** solved in the literature, textbook, test or API statements with a placeholder
upstream proof; **(b)** special cases, small n, weaker variants, recorded by us in
`OpenProofs/Statements/`; **(c)** genuinely open problems, strictly time-boxed. The queue
(`ledger/queue.json`, refilled by `./op refill`) orders targets by tier, then by a rough 1-5
difficulty estimate (category, analytic/deep vocabulary, statement length), then by whether an
external formal proof already exists.

If a proof comes out suspiciously easy, suspect a misformalized upstream statement (Prover
procedure step 7). That is a valuable finding, not a "solved".

## Layout

| Path | What |
|---|---|
| `op`, `scripts/op.py` | The agent CLI (above). |
| `op.config.json` | Parallel-prover configuration (CLI, model, provers, budget). |
| `CLAUDE.md`, `.claude/` | Claude Code entry (`@AGENTS.md`), settings (permissions, env, SessionStart hook), `startup` skill, `prover` agent. |
| `.mcp.json` | Lean LSP MCP server for Claude Code. |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lake project; depends on formal-conjectures pinned to one commit (Mathlib comes with it). |
| `upstream.json` | The pins: formal-conjectures commit, toolchain, Mathlib rev, erdosproblems DB commit. |
| `OpenProofs/Results/<Source>/<Name>.lean` | One module per claimed result (plain, non-`module` Lean files). |
| `OpenProofs/Statements/<Name>.lean` | Self-recorded variant statements (placeholder proofs only). |
| `OpenProofs/Lib/` | Shared helper lemmas (see "Shared helper library"). |
| `OpenProofsChecker/Main.lean` | `opcheck`, the Lean half of the checker (reads `.olean` files). |
| `scripts/check.py`, `scripts/lint.py` | Checker driver and source lint (trusted base). |
| `scripts/triage.py`, `quickkill.py`, `placeholder_deps.py`, `crosscheck_status.py`, `fetch_erdos_db.sh` | Triage and misformalization-lead tools. |
| `scripts/loop.py` | Compatibility shim (`preflight`; everything else forwards to `op`). |
| `claims.json` | What we claim (written by `./op done`/`./op check`). |
| `ledger/results.json`, `ledger/LEDGER.md` | Checker verdicts (machine-written). |
| `ledger/queue.json` | Target queue (one target per line). |
| `ledger/notes/` | Per-target attempt logs. |
| `tests/run_adversarial.py`, `tests/adversarial/`, `tests/mcp_smoke.py` | Checker adversarial suite; MCP smoke test. |
| `outbox/` | Drafts for the owner. Never sent anywhere. |
| `LOOP.md` | One-iteration prompt for scheduled headless runs. |
| `work/` | Gitignored scratch: locks, attempts, try files, index, logs, swarm logs. |

## Setup and environment

- Lean via `elan` (official `elan-init.sh`, `--no-modify-path`). `op` and the Python scripts add
  `~/.elan/bin` to `PATH` themselves; `.claude/settings.json` and `.mcp.json` set a `PATH` that
  includes it (machine-specific absolute paths).
- `release.lean-lang.org` is blocked here by a Cisco Umbrella filter, so `elan` cannot download
  toolchains. v4.33.1 was installed from the GitHub release asset
  (`lean-4.33.1-darwin_aarch64.tar.zst`, sha256 `88c45aad…065a9d`, checked) into
  `~/.elan/toolchains/leanprover--lean4---v4.33.1`. A toolchain bump needs the same manual step.
- `lake exe cache get` fetched Mathlib. Upstream problem modules build on demand (`./op begin`
  and `./op scaffold` do it under the build lock; ~20-60 s each).
- Python: system `python3` (3.9), standard library only. `lean-lsp-mcp` is a `uv tool`.
- Codex: run `codex exec -C <repo> -s workspace-write "startup"`. Its sandbox may refuse writes
  to `.git`; then `./op commit` fails harmlessly and the next Claude Code session commits.

## Checker rules (what PASS means)

A claim passes only if all five layers pass:

1. **integrity**: `lean-toolchain` and the lakefile's formal-conjectures `rev` match `upstream.json`;
   every package in `.lake/packages` is at its manifest revision with a clean working tree
   (tracked and untracked); no `lakefile.lean`; the lakefile sets none of `moreLeanArgs`,
   `weakLeanArgs`, `plugins`, `dynlibs`, `precompileModules`, ... and mentions no `debug.`/`trust`.
2. **lint** (`scripts/lint.py`): result files may import only Mathlib, Batteries, Aesop, Plausible,
   FormalConjectures*, `OpenProofs.Results.*`, `OpenProofs.Lib.*`. Banned in code: placeholder
   proofs, `admit`, `stop`, `axiom`, `opaque`, `unsafe`, `partial`, `implemented_by`, `extern`,
   `export`, `csimp`, `@[init]`, `native_decide`/`+native`, `ofReduceBool`/`trustCompiler`,
   macros/syntax/elaborators/notation, `run_cmd`/`run_tac`/`#eval`, `initialize`, `debug.*`
   options, environment or `Lean.Elab/Meta/Kernel` APIs, `meta`, the `module` header. A critical
   subset is banned even in comments (the lint reads raw text). The lint covers every
   `OpenProofs` module a result imports, including `OpenProofs/Lib/`. Statement files may contain
   only theorem statements whose proof is the placeholder, importing only Mathlib/FormalConjectures.
3. **build**: the candidate modules' build outputs are deleted, then `lake build` rebuilds them.
4. **opcheck** (`OpenProofsChecker/Main.lean`, loads `.olean` files, runs no imported code):
   - `ref_trusted`: the reference is a theorem in the named module, from the pinned
     formal-conjectures package (`upstream`) or `OpenProofs.Statements.*` (`variant`).
   - `theorem_found`: the claimed theorem is a theorem in the claimed module, compiled from this repo.
   - `statement_match`: claimed type is the reference type as an `Expr` ("syntactic"), or the
     kernel accepts `theorem _ : <reference type> := <claimed theorem>` ("kernel-defeq").
   - `statement_consts`: the reference statement uses only trusted constants.
   - `axioms`: full walk of every reachable constant body (does not trust precomputed axiom
     data in `.olean` files); only `propext`, `Classical.choice`, `Quot.sound` allowed.
   - `closure_clean`: results do not import `OpenProofs.Statements.*` or the checker.
   - `candidate_decls`: every declaration from this repo in the closure is under `OpenProofs.`
     (except realized equation lemmas `f.eq_N`/`f.eq_def`/`f.eq_unfold` of trusted definitions),
     is not an axiom/opaque/quot/unsafe/partial/`implemented_by`/`extern`/`export`/`init`
     declaration, and shadows no trusted name (a theorem may mirror a trusted *theorem's* name).
   - `kernel_replay`: each candidate module is replayed through the kernel on top of its imports.
5. **leanchecker**: the toolchain's own `leanchecker` replays each candidate module independently.

Trust assumptions (documented, not checked): the Lean kernel and toolchain binary; Mathlib oleans
from the official cache; upstream oleans built locally from the pinned clean checkout. Deep mode
(`lake env leanchecker --fresh <module>`, replays all of Mathlib) is available but slow and unrun.

`tests/run_adversarial.py` must pass before any verdict is trusted. Results record the
`trusted_base_sha256` (lakefile, toolchain, manifest, upstream.json, checker sources, check.py,
lint.py) they were checked under; `./op finish/done` refuses a stale PASS.

**Changing the trusted base** (anything in that hash, or relaxing a rule) needs the owner's
approval, a new adversarial case for any new rule, a full adversarial run
(`./op preflight --full`), and `./op recheck`.

**Loop sessions never edit tooling.** `.claude/settings.json` denies edits to the checker,
`scripts/`, `tests/`, `.claude/`, `.mcp.json`, `op.config.json`, `AGENTS.md`, the Lake files
and `.lake/` (a deny never prompts). If you find a tooling bug, record it with a proposed fix in
`docs/TODO.md` and carry on. Tooling changes are maintenance work done in an owner-approved
session (for example one started outside this directory, or after the owner edits the settings).

## Shared helper library

`OpenProofs/Lib/*.lean` holds reusable, fully proved lemmas (namespace `OpenProofs.Lib`), e.g.
`OpenProofs.Lib.mono_triple_of_six_le_card` (`Lib/Graph.lean`, the pigeonhole step of R(3,3)) and p-adic
valuation of sums (`Lib/Padic.lean`). Same rules as result files. The checker accepts a Lib
module through every result that imports it: lint, declaration rules, axioms and kernel replay
cover the whole import closure, so a placeholder anywhere in an imported Lib module rejects the
result (adversarial cases `LibSorryUse`, `LibSorryUnused`). Check a new Lib file with
`./op try OpenProofs/Lib/<File>.lean` before importing it.

## Variants, value questions, assessments

**Variants (tier b):** put the exact statement in `OpenProofs/Statements/<Name>.lean` as
`theorem OpenProofs.Statements.<Name>.<thm> : <statement> := by` followed by the placeholder;
the claim uses `ref_kind: "variant"` (`./op check <claim-id>` after adding the claim to
`claims.json` by hand). For a special case obtained by fixing arguments of an upstream statement,
write the type as `type_of% (Upstream.thm arg₁ arg₂)`: the elaborated type is then mechanically
the upstream body with those arguments substituted (see `OpenProofs/Statements/Erdos828.lean`).

**Value questions:** an upstream statement that mentions `<thm>.answer` (a `def` whose body is the
placeholder) can never pass the axiom check. Do not "fill in" answers (`./op refill` skips these).
If such a statement is false for every possible answer (e.g. a constant answer for a quantity
that depends on a quantified parameter: Erdős 142, 319, 321, 361, 409, 450, 503, 552, 692),
record the answer-free negation as a variant and assess it `possible-misformalization`.

Assessments: `proved`, `special-case` (variant), `possible-misformalization` (formal statement
proved but it does not capture the informal problem; draft `outbox/misformalization-<id>.md`).

## Boundaries

- No PRs, issues, comments, posts, emails or any submission upstream or elsewhere (Claude Code
  settings deny `git push`, `gh`, `curl`, posting connectors). Drafts go in `outbox/`.
- Do not use the retired `_AI` vault. Scratch goes in gitignored `work/`.
- Git: work on a task branch (`./op branch`), commit there (`./op commit`, `./op done`); never
  merge into `main` or push unless the owner says so.
- Do not edit `.lake/packages/*` (integrity fails; restore with
  `git -C .lake/packages/<pkg> checkout -- . && git -C .lake/packages/<pkg> clean -fd`).
- Bumping the upstream pin: update `lakefile.toml` rev and `upstream.json` together, `lake update`,
  check `lean-toolchain`/Mathlib rev against upstream's, rebuild, run the full adversarial suite
  and `./op recheck`; results whose upstream statement changed must be re-verified.

## Hands-free UI testing

Not applicable: this project has no UI.
