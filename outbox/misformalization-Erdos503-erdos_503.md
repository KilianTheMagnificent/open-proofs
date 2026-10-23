# Possible misformalization: Erdős 503 (`Erdos503.erdos_503`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/503.lean`
- Informal source: https://www.erdosproblems.com/503
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
def erdos_503.answer : ℕ := sorry
theorem erdos_503 (n : ℕ) :
    IsGreatest {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)} erdos_503.answer
```

## Informal statement

"What is the size of the largest A ⊆ ℝ^n such that every three points from A determine an isosceles
triangle?" The answer depends on the dimension `n` (the same file states the values 6 for `n = 2`
and 8 for `n = 3`, and bounds `C(n+1, 2) ≤ … ≤ C(n+2, 2)`).

## Why they differ

`erdos_503.answer : ℕ` is one number for every dimension. In `ℝ^0` every set has at most one point,
so the maximum is at most 1, while in `ℝ^1` a two-point set is isosceles (vacuously), so the maximum
is at least 2. (Upstream's own solved variants `R2` and `R3` give 6 and 8, which also contradict
each other under `erdos_503`.)

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos503.lean`,
  `OpenProofs.Statements.Erdos503.erdos_503.no_constant_answer :
   ∀ a : ℕ, ¬ ∀ n : ℕ, IsGreatest {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)} a`.
- Proof: `OpenProofs/Results/Erdos/P503_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch copy `work/scratch/agentAudit/p503.lean`).
- Checker verdict: PASS on all five layers (coordinator run, 2026-10-23; see `ledger/LEDGER.md`).
- The literal negation `¬ type_of% @Erdos503.erdos_503` follows from the answer-free form in one line (`fun h => erdos_503.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_503.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

`def erdos_503.answer : ℕ → ℕ := sorry` and `IsGreatest {…} (erdos_503.answer n)`.
