# Possible misformalization: Erdős 692 (`Erdos692.erdos_692.parts.ii`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`,
  `FormalConjectures/ErdosProblems/692.lean`
- Informal source: https://www.erdosproblems.com/692
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although
  the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value
  the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
def exactlyOneDivisorIn (n m : ℕ) : Set ℕ :=
  {x | {d ∈ Set.Ioo n m | d ∣ x}.ncard = 1}
def IsDelta₁ (n m : ℕ) (δ : ℝ) : Prop :=
  (exactlyOneDivisorIn n m).HasDensity δ
def erdos_692.parts.ii.answer : ℕ := sorry
theorem erdos_692.parts.ii (n : ℕ) :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ n '' Set.Ioi (n + 1)) (δ n erdos_692.parts.ii.answer)
```

## Informal statement

"Let δ₁(n, m) be the density of the set of integers with exactly one divisor in (n, m). For fixed
n, where does δ₁(n, m) achieve its maximum?" The location of the maximum is a function of `n`.

## Why they differ

`erdos_692.parts.ii.answer : ℕ` is one number `m₀` for every `n`. Take `n = m₀`: the interval
`(m₀, m₀)` is empty, so `δ₁(m₀, m₀) = 0`, while `δ₁(m₀, m₀ + 2)` is the density of multiples of
`m₀ + 1`, i.e. `1/(m₀ + 1) > 0`, and `m₀ + 2 > m₀ + 1` is in the range of the maximum. So
`IsGreatest` fails at `n = m₀`. The hypothesis `∀ a b, IsDelta₁ a b (δ a b)` is satisfiable (every
`exactlyOneDivisorIn a b` is periodic with period `b!`, hence has a natural density), so the
statement is not vacuous and its negation holds for every value of the placeholder.

## Lean evidence

- Variant statement: `OpenProofs/Statements/Erdos692.lean`,
  `OpenProofs.Statements.Erdos692.erdos_692.parts.ii.no_constant_answer :
   ∀ m₀ : ℕ, ¬ ∀ (n : ℕ), ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
     IsGreatest (δ n '' Set.Ioi (n + 1)) (δ n m₀)`.
- Proof: `OpenProofs/Results/Erdos/P692_parts_ii_no_constant_answer.lean` (includes a general
  lemma: a periodic subset of ℕ has natural density `count/L`). `#print axioms`:
  [propext, Classical.choice, Quot.sound] (scratch copy `work/scratch/agentAudit/p692.lean`).
- Checker verdict: PASS on all five layers (coordinator run, 2026-10-23; see `ledger/LEDGER.md`).
- The literal negation `¬ type_of% @Erdos692.erdos_692.parts.ii` follows in one line, but mentions
  `erdos_692.parts.ii.answer`, whose body is a placeholder, so this project's axiom check would
  reject it. The answer-free form is strictly stronger.

## Suggested fix

```lean
def erdos_692.parts.ii.answer : ℕ → ℕ := sorry
theorem erdos_692.parts.ii (n : ℕ) :
    ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      erdos_692.parts.ii.answer n ∈ Set.Ioi (n + 1) ∧
      IsGreatest (δ n '' Set.Ioi (n + 1)) (δ n (erdos_692.parts.ii.answer n))
```

(The membership conjunct also stops a degenerate answer outside the range from matching the
maximal value. Given Cambie's result that there are many local maxima, an asymptotic form may be
more useful.)
