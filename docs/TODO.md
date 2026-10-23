# TODO

Updated: 2026-10-23 (first iteration). Branch `task/first-iteration` (not merged, not pushed).

## Done

- Setup: elan 4.2.4; Lean toolchain v4.33.1 installed by hand from the GitHub release asset
  (sha256 checked) because `release.lean-lang.org` is blocked on this network (Cisco Umbrella);
  Lake project depending on formal-conjectures `96343eeb` (Mathlib `0df444a3`, v4.33.1);
  `lake exe cache get` done; all 957 upstream `ErdosProblems` modules built locally.
- Checker: `OpenProofsChecker/Main.lean` (`opcheck`) + `scripts/check.py` + `scripts/lint.py`.
  Five layers: integrity, lint, clean build, opcheck (statement identity incl. kernel-defeq
  bridge, full-walk axioms, candidate-declaration rules, kernel replay), leanchecker.
- Adversarial suite `tests/run_adversarial.py`: RESULTS_PLACEHOLDER
- Triage: `scripts/triage.py` (all placeholder theorems → `work/candidates.json`),
  `scripts/crosscheck_status.py` (→ `ledger/status-crosscheck.md`), `scripts/quickkill.py`.
- Loop: `scripts/loop.py`, `LOOP.md`, `ledger/queue.json`.
- Results: see `ledger/LEDGER.md`.

## Remaining

- REMAINING_PLACEHOLDER

## Next safe action

NEXT_PLACEHOLDER

## Checks

CHECKS_PLACEHOLDER
