# Possible misformalization: Erdős 319 (`Erdos319.erdos_319`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/319.lean`
- Informal source: https://www.erdosproblems.com/319
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
def erdos_319.answer : ℕ := sorry
theorem erdos_319 (N : ℕ) : IsGreatest
    { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) }
    erdos_319.answer
```

## Informal statement

"What is the size of the largest A ⊆ {1, …, N} such that there is a function δ : A → {-1, 1}
such that ∑_{n∈A} δ(n)/n = 0 and ∑_{n∈A'} δ(n)/n ≠ 0 for all non-empty A' ⊊ A?" The answer is a
function of `N` (the file's own `isTheta` variant says it is `Θ(N)`).

## Why they differ

`erdos_319.answer : ℕ` is one number for all `N`. For `N = 1` every `A ⊆ {1}` has at most one
element, so the maximum is at most 1; for `N = 6`, `A = {2, 3, 6}` with `δ = (+1, -1, -1)` has
`1/2 - 1/3 - 1/6 = 0` and no vanishing proper non-empty subsum, so the maximum is at least 3.
Hence no value of the placeholder makes `∀ N, IsGreatest … answer` true.

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos319.lean`,
  `OpenProofs.Statements.Erdos319.erdos_319.no_constant_answer : ∀ a : ℕ, ¬ ∀ N : ℕ, IsGreatest {…} a`
  (upstream body with the placeholder replaced by a bound `a`).
- Proof: `OpenProofs/Results/Erdos/P319_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch copy `work/scratch/agentAudit/p319b.lean`).
- Checker verdict: PASS on all five layers (coordinator run, 2026-10-23; see `ledger/LEDGER.md`).
- The literal negation `¬ type_of% @Erdos319.erdos_319` follows from the answer-free form in one line (`fun h => erdos_319.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_319.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

```lean
def erdos_319.answer : ℕ → ℕ := sorry
theorem erdos_319 (N : ℕ) : IsGreatest {…} (erdos_319.answer N)
```
