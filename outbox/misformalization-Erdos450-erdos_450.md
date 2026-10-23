# Possible misformalization: Erdős 450 (`Erdos450.erdos_450`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/450.lean`
- Informal source: https://www.erdosproblems.com/450
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
noncomputable def windowThreshold (ε : ℝ) (n : ℕ) : ℕ∞ :=
  ⨅ y : {y : ℕ // ∀ z ≥ y, UniformlySparse ε n z}, (y.1 : ℕ∞)
def erdos_450.answer : ℕ∞ := sorry
theorem erdos_450 (ε : ℝ) (hε : 0 < ε) (n : ℕ) : windowThreshold ε n = erdos_450.answer
```

## Informal statement

"How large must y = y(ε, n) be such that the number of integers in (x, x + y) with a divisor in
(n, 2n) is at most εy?" The answer is a function of `ε` and `n`.

## Why they differ

`erdos_450.answer : ℕ∞` is one value for all `ε > 0` and all `n`. For `ε = 1` every window is
sparse (the open window `(x, x + z)` contains fewer than `z` integers), so
`windowThreshold 1 2 = 0`. For `ε = 1/4` and `n = 2`, the window `(2, 4) = {3}` (`x = 2`, `z = 2`)
contains `3`, which has the divisor `3 ∈ (2, 4)`, and `1 > 2/4`, so the threshold `0` fails and
`windowThreshold (1/4) 2 ≠ 0`.

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos450.lean`,
  `OpenProofs.Statements.Erdos450.erdos_450.no_constant_answer :
   ∀ a : ℕ∞, ¬ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, windowThreshold ε n = a`.
- Proof: `OpenProofs/Results/Erdos/P450_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch copy `work/scratch/agentAudit/p450.lean`).
- Checker verdict: not run by the auditing agent.
- The literal negation `¬ type_of% @Erdos450.erdos_450` follows from the answer-free form in one line (`fun h => erdos_450.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_450.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

`def erdos_450.answer : ℝ → ℕ → ℕ∞ := sorry` with `windowThreshold ε n = erdos_450.answer ε n`, or,
closer to the intent ("how large must y be", known to be `O_ε(n)`), an asymptotic statement in `n`
for fixed `ε`.
