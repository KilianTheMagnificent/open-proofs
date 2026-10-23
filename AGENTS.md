# open-proofs: agent instructions

This file and `docs/TODO.md` are the project's only agent memory. Read both before working.
Also read `~/Developer/Projects/AGENTS.md` (parent rules); this file overrides it where they differ.

## Purpose

A recurring, bottomless token sink with a perfect external oracle: machine-checked Lean 4 proofs
of statements from google-deepmind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(Erdős problems and similar) whose upstream proof is still a placeholder. Nobody reviews the
output by hand. **The checker is the review**, so its integrity matters more than any result.

Tiers of targets:

- **(a)** solved in the literature (or textbook), upstream statement still a placeholder:
  formalize the known proof.
- **(b)** special cases, small n, weaker variants. If upstream has no such statement, record it
  yourself as a *named variant* in `OpenProofs/Statements/` (see below).
- **(c)** genuinely open problems: strictly time-boxed; expect no progress.

If a proof comes out suspiciously easy, suspect a misformalized upstream statement: compare
with the informal problem (docstring, erdosproblems.com, the cited paper) and record the claim
with assessment `possible-misformalization`, not `proved`. Draft a report in `outbox/`.

## Layout

| Path | What |
|---|---|
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lake project; depends on formal-conjectures pinned to one commit (Mathlib comes with it). |
| `upstream.json` | The pins: formal-conjectures commit, toolchain, Mathlib rev, erdosproblems DB commit. |
| `OpenProofs/Results/<Source>/<Name>.lean` | One module per claimed result. Plain (non-`module`) Lean files. |
| `OpenProofs/Statements/<Name>.lean` | Self-recorded variant statements (theorem statements with placeholder proofs only). |
| `OpenProofs/Lib/` | Shared helper lemmas for results (optional; same rules as results). |
| `OpenProofsChecker/Main.lean` | `opcheck`, the Lean half of the checker (reads `.olean` files). |
| `scripts/check.py` | Checker driver: runs all five layers, records verdicts. |
| `scripts/lint.py` | Source lint used by the checker. |
| `scripts/triage.py` | Lists upstream placeholder theorems into `work/candidates.json`. |
| `scripts/quickkill.py` | Cheap-automation sweep over upstream statements (misformalization leads). |
| `scripts/loop.py` | Queue management and the deterministic loop steps. |
| `claims.json` | What we claim: result module/theorem and the reference it must match. |
| `ledger/results.json`, `ledger/LEDGER.md` | Checker verdicts (machine-written by `check.py --record`). |
| `ledger/queue.json` | Target queue with status and attempt history. |
| `tests/run_adversarial.py`, `tests/adversarial/` | Adversarial suite proving the checker rejects each cheat. |
| `outbox/` | Drafts for the owner (misformalization reports, write-ups). Never sent anywhere. |
| `LOOP.md` | The prompt for one resumable loop iteration. |
| `work/` | Gitignored scratch (reference clone, erdos DB copy, quick-kill output, logs). |

## Setup and environment

- Lean via `elan` (installed with the official `elan-init.sh`, `--no-modify-path`). Commands need
  `export PATH="$HOME/.elan/bin:$PATH"`; the Python scripts add it themselves.
- On this network `release.lean-lang.org` is blocked by a Cisco Umbrella filter, so `elan` cannot
  download toolchains. The pinned toolchain was installed from the GitHub release asset
  (`lean-4.33.1-darwin_aarch64.tar.zst`, sha256 `88c45aad…065a9d`, checked) into
  `~/.elan/toolchains/leanprover--lean4---v4.33.1`. A toolchain bump needs the same manual step.
- `lake exe cache get` fetches Mathlib oleans. Upstream problem files are built locally
  (`lake build 'FormalConjectures.ErdosProblems.«N»'`, ~20-30 s each after the first).
- Python: system `python3` (3.9), standard library only.

## How to run

```bash
python3 scripts/loop.py preflight [--full]   # integrity + adversarial tests (--full: Lean cases too, ~6 min)
python3 scripts/check.py --claim ID [--record]
python3 scripts/check.py --all --record      # re-check every claim, rewrite the ledger
python3 tests/run_adversarial.py             # whole adversarial suite (~7 min)
python3 scripts/triage.py                    # refresh work/candidates.json
python3 scripts/quickkill.py --subdir ErdosProblems --resume --workers 4
python3 scripts/loop.py next | status | finish ID --outcome ... [--claim ...] --notes ...
```

Iterate on a proof with `lake env lean OpenProofs/Results/.../X.lean` (no build products). Only
one process should run `lake build` / `check.py` at a time in this workspace.

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
   subset is banned even in comments (the lint reads raw text for it), so do not mention those
   words in result files at all. Statement files may contain only theorem statements whose proof
   is the placeholder, importing only Mathlib/FormalConjectures.
3. **build**: the candidate modules' build outputs are deleted, then `lake build` rebuilds them.
4. **opcheck** (`OpenProofsChecker/Main.lean`, loads `.olean` files, runs no imported code):
   - `ref_trusted`: the reference is a theorem in the named module, from the pinned
     formal-conjectures package (`upstream`) or `OpenProofs.Statements.*` (`variant`).
   - `theorem_found`: the claimed theorem is a theorem in the claimed module, compiled from this repo.
   - `statement_match`: claimed type is the reference type as an `Expr` ("syntactic"), or the
     kernel accepts `theorem _ : <reference type> := <claimed theorem>` ("kernel-defeq", e.g. a
     different but definitionally equal instance path). Recorded per result.
   - `statement_consts`: the reference statement uses only trusted constants.
   - `axioms`: full walk of every reachable constant body (does not trust precomputed axiom
     data in `.olean` files); only `propext`, `Classical.choice`, `Quot.sound` allowed.
   - `closure_clean`: results do not import `OpenProofs.Statements.*` or the checker.
   - `candidate_decls`: every declaration from this repo in the closure is under `OpenProofs.`,
     is not an axiom/opaque/quot/unsafe/partial/`implemented_by`/`extern`/`export`/`init`
     declaration, and shadows no trusted name (a theorem may mirror a trusted *theorem's* name).
   - `kernel_replay`: each candidate module is replayed through the kernel on top of its imports.
5. **leanchecker**: the toolchain's own `leanchecker` replays each candidate module independently.

Trust assumptions (documented, not checked): the Lean kernel and toolchain binary; Mathlib oleans
from the official cache; upstream oleans built locally from the pinned clean checkout. Deep mode
(`lake env leanchecker --fresh <module>`, replays all of Mathlib) is available but slow and unrun.

`tests/run_adversarial.py` must pass before any verdict is trusted. Results record the
`trusted_base_sha256` (lakefile, toolchain, manifest, upstream.json, checker sources, check.py,
lint.py) they were checked under; `loop.py finish --outcome proved` refuses a stale PASS.

**Changing the trusted base** (anything in that hash, or relaxing a rule) needs the owner's
approval, a new adversarial case for any new rule, a full adversarial run, and `--all --record`.

## Writing a result

1. Pick a target (`loop.py next`), read the upstream file and its informal source.
2. Create `OpenProofs/Results/<Source>/<Name>.lean`: `import` the upstream module, a module
   docstring, `open <UpstreamNamespace>` *before* `namespace OpenProofs.<UpstreamNamespace>`
   (inside it, `<UpstreamNamespace>` resolves to `OpenProofs.<UpstreamNamespace>`; or write
   `open _root_.<UpstreamNamespace>`), and the theorem with the upstream statement copied
   verbatim (same name as upstream, e.g. `OpenProofs.Erdos292.erdos_292.variants.mul`). Local
   notation from upstream must be expanded by hand (e.g. `R(3, 3)` is
   `SimpleGraph.classicalRamsey 3 3`). Helpers get distinctive names; never redefine an upstream name.
3. Iterate with `lake env lean <file>`. Never cite an upstream placeholder theorem.
4. Add a claim to `claims.json` (`id`, `module`, `theorem`, `ref_kind`, `ref_module`,
   `ref_theorem`, `tier`, `assessment`, `summary`, `notes`), then
   `python3 scripts/check.py --claim ID --record`.
5. Close the queue entry with `loop.py finish`, update `docs/TODO.md`, commit on the task branch.

**Variants (tier b):** put the exact statement in `OpenProofs/Statements/<Name>.lean` as
`theorem OpenProofs.Statements.<Name>.<thm> : <statement> := by` followed by the placeholder;
the claim uses `ref_kind: "variant"`. For a special case obtained by fixing arguments of an
upstream statement, write the type as `type_of% (Upstream.thm arg₁ arg₂)`: the elaborated type
is then mechanically the upstream body with those arguments substituted (see
`OpenProofs/Statements/Erdos828.lean`). Name what it specializes in the docstring and in the claim's
`notes`. The ledger shows it as a variant; never present it as the upstream problem.

Assessments: `proved` (matches upstream and the informal problem), `special-case` (variant),
`possible-misformalization` (formal statement proved but it does not capture the informal problem;
draft `outbox/misformalization-<id>.md`).

## Boundaries

- No PRs, issues, comments, posts, emails or any submission upstream or elsewhere. Write drafts
  in `outbox/` for the owner to approve.
- Do not use the retired `_AI` vault. Scratch goes in gitignored `work/`.
- Git: work on a task branch, commit there; do not merge into `main` or push unless the owner says so.
- Do not edit `.lake/packages/*` (the integrity layer will fail; restore with
  `git -C .lake/packages/<pkg> checkout -- . && git -C .lake/packages/<pkg> clean -fd`).
- Bumping the upstream pin: update `lakefile.toml` rev and `upstream.json` together, `lake update`,
  check `lean-toolchain`/Mathlib rev against upstream's, rebuild, run the full adversarial suite
  and `check.py --all --record`; results whose upstream statement changed must be re-verified.
- Analysis only for anything financial (parent rule); not applicable here.

## Hands-free UI testing

Not applicable: this project has no UI.
