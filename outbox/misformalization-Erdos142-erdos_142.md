# Possible misformalization: Erdős 142 (`Erdos142.erdos_142`, `Erdos142.erdos_142.variants.isTheta`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/142.lean`
- Informal source: https://www.erdosproblems.com/142
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
abbrev r := Set.IsAPOfLengthFree.maxCard
def erdos_142.answer : ℕ → ℝ := sorry
theorem erdos_142 (k : ℕ) : (fun N => (r k N : ℝ)) ~[atTop] erdos_142.answer

def erdos_142.variants.isTheta.answer : ℕ → ℝ := sorry
theorem erdos_142.variants.isTheta (k : ℕ) :
    (fun N => (r k N : ℝ)) =Θ[atTop] erdos_142.variants.isTheta.answer
```

## Informal statement

"Prove an asymptotic formula for r_k(N), the largest possible size of a subset of {1, …, N} that
does not contain any non-trivial k-term arithmetic progression. That is, find f_k with
r_k(N)/f_k(N) → 1" (and, for the variant, "find f_k with r_k(N) ≍_k f_k(N)"). The answer `f_k`
depends on `k`.

## Why they differ

`answer : ℕ → ℝ` is a function of `N` only, and the theorem quantifies over every `k : ℕ` (no
lower bound on `k`). Upstream already proves `r 0 N = N` (`Set.IsAPOfLengthFree.maxCard_zero`),
and `r 2 N ≤ 1` because any two distinct elements form a 2-term progression. A common `g` with
`r 0 ~ g` and `r 2 ~ g` would give `N ~ r 2 N ≤ 1`, which is false; likewise `N =Θ r 2 N` is false.
So both statements are refutable for every choice of the placeholder, by an argument that has
nothing to do with the problem (Roth/Szemerédi-type bounds are never used).

## Lean evidence

- Variant statements (answer-free negations):
  `OpenProofs/Statements/Erdos142.lean`:
  `OpenProofs.Statements.Erdos142.erdos_142.no_constant_answer :
   ∀ g : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (r k N : ℝ)) ~[atTop] g` and
  `OpenProofs.Statements.Erdos142.erdos_142.variants.isTheta.no_constant_answer` (same with `=Θ[atTop]`).
- Proofs: `OpenProofs/Results/Erdos/P142_no_constant_answer.lean`,
  `OpenProofs/Results/Erdos/P142_isTheta_no_constant_answer.lean`.
  `#print axioms`: [propext, Classical.choice, Quot.sound] for both (also checked in `work/scratch/agentAudit/p142.lean`).
- Checker verdict: not run by the auditing agent (the coordinator runs `scripts/check.py`).
- The literal negation `¬ type_of% @Erdos142.erdos_142` follows from the answer-free form in one line (`fun h => erdos_142.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_142.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

Let the answer depend on `k` and restrict to the meaningful range, e.g.

```lean
def erdos_142.answer : ℕ → ℕ → ℝ := sorry
theorem erdos_142 (k : ℕ) (hk : 3 ≤ k) :
    (fun N => (r k N : ℝ)) ~[atTop] erdos_142.answer k
```

and the same for `erdos_142.variants.isTheta`. (`erdos_142.variants.lower` already has `1 < k`;
`erdos_142.variants.three` fixes `k = 3` and is fine.)
