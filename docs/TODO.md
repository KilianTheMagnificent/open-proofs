# TODO

Updated 2026-10-23 (end of the first iteration). Branch `task/first-iteration` (not merged into
`main`, not pushed). Agent memory for this project = `AGENTS.md` + this file.

## Done

- **Setup.** elan 4.2.4 (`--no-modify-path`); Lean v4.33.1 installed by hand from the GitHub
  release asset (sha256 checked) because `release.lean-lang.org` is blocked here by a Cisco
  Umbrella filter. Lake project depends on formal-conjectures `96343eeb` (pinned in
  `lakefile.toml` + `upstream.json`; Mathlib `0df444a3` comes with it). `lake exe cache get`
  done; all 957 upstream `ErdosProblems` modules plus `Wikipedia.{RamseyNumbers,CongruentNumber,
  RamanujanTau}` and `WrittenOnTheWallII.Test` built locally.
- **Checker** (`scripts/check.py` + `OpenProofsChecker/Main.lean` + `scripts/lint.py`): five
  layers (integrity, lint, clean build, opcheck, leanchecker); see AGENTS.md "Checker rules".
- **Adversarial suite** `tests/run_adversarial.py`: 45/45 expectations hold (10 lint, 9 integrity,
  26 Lean cases incl. sorry, sorry via upstream, native_decide, custom axiom, axiom-as-claim,
  weakened statement, shadowed upstream definition, instance override, implemented_by, extern,
  opaque, unsafe/partial, `debug.skipKernelTC` environment hack (caught only by kernel replay and
  leanchecker), macro-hidden sorry, importing a statement file, outside-namespace and
  upstream-namespace helpers, fake equation lemma, wrong reference kinds, statement using a
  candidate definition, broken proof, 3 positive controls).
- **Triage tools:** `scripts/triage.py` (4343 placeholder theorems → `work/candidates.json`),
  `scripts/crosscheck_status.py` (46 upstream-vs-erdosproblems.com disagreements →
  `ledger/status-crosscheck.md`), `scripts/quickkill.py` (all 2619 Erdős placeholder statements
  and their negations vs `omega|decide|norm_num|simp|trivial|aesop`: 1 hit, `1193.sumRep_univ`,
  legitimately easy), `scripts/placeholder_deps.py` (645 written upstream proofs scanned, 22 rest
  on placeholders → `ledger/placeholder-deps.md`).
- **Loop:** `LOOP.md` (prompt), `scripts/loop.py` (preflight/next/finish/status/recheck),
  `ledger/queue.json`.
- **Results:** 35 claims, all PASS (see `ledger/LEDGER.md`): 22 tier-a upstream placeholders
  proved, 2 tier-b special cases (Erdős 828 at a = 0, −1), 11 possible misformalizations
  (answer-free negations of open `question value` statements whose placeholder answer cannot
  depend on a quantified parameter: Erdős 142 (×2), 319, 321, 361, 409 (×2), 450, 503, 552, 692).
- **Outbox drafts** (nothing sent): `writeup-first-iteration.md`, 10 `misformalization-*.md`
  (incl. 506, conditional, no result file), `note-RamanujanTau-tau_one-rests-on-placeholder.md`.

## Remaining

- Queue (`python3 scripts/loop.py status`): pending tier a: Erdős 767 czipszer, 1084
  easy_upper_d2, 1052 unitary-perfect test, 675, 18, BusyBeaver.BB_1, 902 szekeres_f_three;
  tier c: Erdős 828 at a = 1, 349 floor_3_halves_odd. Refill from `work/candidates.json`
  (regenerate with `scripts/triage.py`) and `ledger/placeholder-deps.md` leads (e.g. prove
  `Erdos633.IsCuttable.of_isSquare`, `Erdos1052.isUnitaryPerfect_87360` dependencies).
- Erdős 506: the no-constant-answer refutation is proved only conditionally on upstream's
  placeholder `erdos_506.variants.large_n` (Elliott); needs an unconditional argument or stays a
  draft. 409.parts.iii and 975.variants.quadratic: suspected issues without Lean proof (see the
  506/409 drafts and the audit notes in the claims).
- Extend the quick-kill and placeholder-deps sweeps beyond `ErdosProblems` (build the other
  upstream directories first: `lake build FormalConjectures` takes a while).
- Re-verify external `formal_proof` links (39 "upstream solved, DB open" rows cite them) by porting
  the linked Lean files and running this checker: high-value, needs toolchain/Mathlib porting.
- Deep check not run: `lake env leanchecker --fresh <module>` (replays all of Mathlib; slow).
- Owner decisions: whether to publish this repo (needed for any `formal_proof` URL), whether to
  send any outbox draft, whether to merge `task/first-iteration` into `main`.

## Next safe action

`python3 scripts/loop.py preflight --full`, then `python3 scripts/loop.py next` and follow
`LOOP.md`. Before the first loop run on a new day, `python3 scripts/check.py --all --record` keeps
the ledger's trusted-base hashes current.

## Checks (this iteration)

- Passed: `tests/run_adversarial.py` 45/45 (after the last checker change);
  `scripts/check.py --all --record` 35/35 PASS under the current trusted base; `scripts/check.py --integrity` OK.
- Not run: `leanchecker --fresh` deep replay; quick-kill/placeholder sweeps on non-Erdős
  directories; any upstream submission (out of scope by rule).
