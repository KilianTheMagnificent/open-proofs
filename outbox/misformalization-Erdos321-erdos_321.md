# Possible misformalization: Erdős 321 (`Erdos321.erdos_321`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/321.lean`
- Informal source: https://www.erdosproblems.com/321
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
noncomputable def R (N : ℕ) : ℕ :=
  sSup { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : Set.InjOn (fun (S : Finset ℕ) ↦ ∑ n ∈ S, (1 : ℚ) / n) A.powerset) }
def erdos_321.answer : ℕ := sorry
theorem erdos_321 (N : ℕ) : R N = erdos_321.answer
```

## Informal statement

"Let R(N) be the size of the largest A ⊆ {1, …, N} such that all sums ∑_{n∈S} 1/n are distinct for
S ⊆ A. What is R(N)?" The answer is a function of `N`.

## Why they differ

`erdos_321.answer : ℕ` is one number, so the theorem says `R` is constant. But `R 0 = 0` (only the
empty set fits in `Finset.Icc 1 0`) and `R 1 ≥ 1` (`{1}` has subset sums `0` and `1`). The file's
own `variants.lower` (Bleicher–Erdős) also makes `R N` unbounded.

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos321.lean`,
  `OpenProofs.Statements.Erdos321.erdos_321.no_constant_answer : ∀ a : ℕ, ¬ ∀ N : ℕ, R N = a`.
- Proof: `OpenProofs/Results/Erdos/P321_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound]
  (scratch copy `work/scratch/agentAudit/p321.lean`).
- Checker verdict: PASS on all five layers (coordinator run, 2026-10-23; see `ledger/LEDGER.md`).
- The literal negation `¬ type_of% @Erdos321.erdos_321` follows from the answer-free form in one line (`fun h => erdos_321.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_321.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

```lean
def erdos_321.answer : ℕ → ℕ := sorry
theorem erdos_321 : R = erdos_321.answer
```
(or `∀ N, R N = erdos_321.answer N`). The asymptotic variants already use `ℕ → ℝ` answers and are
fine.
