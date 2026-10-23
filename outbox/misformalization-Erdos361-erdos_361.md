# Possible misformalization: Erdős 361 (`Erdos361.erdos_361`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/361.lean`
- Informal source: https://www.erdosproblems.com/361
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
noncomputable def subsetSumAvoidanceNumber (c : ℝ) (n : ℕ) : ℕ :=
  maxSubsetSumAvoidingCard ⌊c * n⌋₊ n
def erdos_361.answer : ℕ → ℕ := sorry
theorem erdos_361 (c : ℝ) (hc : 0 < c) :
    subsetSumAvoidanceNumber c = erdos_361.answer
```

## Informal statement

"Let c > 0 and n be some large integer. What is the size of the largest set
A ⊆ {1, …, ⌊cn⌋} such that n is not a sum of a subset of A? Does this depend on n in an irregular
way?" The answer depends on both `c` and `n`.

## Why they differ

`erdos_361.answer : ℕ → ℕ` takes only `n`, but the theorem quantifies over every `c > 0`, so it
says the quantity does not depend on `c`. At `n = 2`: with `c = 1/4` the range is
`{1, …, ⌊1/2⌋} = ∅`, so the value is `0`; with `c = 1` the range is `{1, 2}` and `{1}` avoids the
sum `2`, so the value is `1` (both computed by `decide` on the upstream computable
`maxSubsetSumAvoidingCard`). Note also that equality of functions makes the claim about every `n`,
including small `n`, while the problem concerns large `n`.

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos361.lean`,
  `OpenProofs.Statements.Erdos361.erdos_361.no_constant_answer :
   ∀ a : ℕ → ℕ, ¬ ∀ c : ℝ, 0 < c → subsetSumAvoidanceNumber c = a`.
- Proof: `OpenProofs/Results/Erdos/P361_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch copy `work/scratch/agentAudit/p361.lean`).
- Checker verdict: not run by the auditing agent.
- The literal negation `¬ type_of% @Erdos361.erdos_361` follows from the answer-free form in one line (`fun h => erdos_361.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_361.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

```lean
def erdos_361.answer : ℝ → ℕ → ℕ := sorry
theorem erdos_361 (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n in atTop, subsetSumAvoidanceNumber c n = erdos_361.answer c n
```
(or an asymptotic form; "for large n" suggests `∀ᶠ`).
