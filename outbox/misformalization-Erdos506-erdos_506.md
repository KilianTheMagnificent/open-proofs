# Possible misformalization: Erdős 506 (`Erdos506.erdos_506`, `Erdos506.erdos_506.variants.small_n`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`,
  `FormalConjectures/ErdosProblems/506.lean`
- Informal source: https://www.erdosproblems.com/506
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although
  the quantity asked for depends on `n`.

## Upstream Lean statement

```lean
def erdos_506.answer : ℕ := sorry
theorem erdos_506 (n : ℕ) (hn : 4 ≤ n) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      erdos_506.answer

def erdos_506.variants.small_n.answer : ℕ := sorry
theorem erdos_506.variants.small_n (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 393) :
    IsLeast { … same set … } erdos_506.variants.small_n.answer
```

The same file states the solved variant (Elliott, corrected by Purdy–Smith)

```lean
def erdos_506.variants.large_n.answer (n : ℕ) : ℕ := (n - 1).choose 2 + 1 - (n - 1) / 2
theorem erdos_506.variants.large_n (n : ℕ) (hn : 393 < n) :
    IsLeast { … same set … } (erdos_506.variants.large_n.answer n)
```

## Informal statement

"What is the minimum number of circles determined by any n points in ℝ², not all on a circle?"
The answer is a function of `n`.

## Why they differ

`erdos_506.answer : ℕ` is one number for every `n ≥ 4`, but the file's own `large_n.answer` is a
function of `n` that takes different values at `n = 394` and `n = 395` (`76833` vs `77225`). So
`erdos_506` contradicts `erdos_506.variants.large_n` (Elliott's theorem) for every value of the
placeholder. `small_n` has the same defect on `4 ≤ n ≤ 393` (the minimum is at most `C(4, 3) = 4`
at `n = 4`, since a circle through three of four points is determined by them, but grows roughly
like `n²/2`), although I did not formalize a lower bound to refute it outright.

## Lean evidence (conditional; no result file written)

`work/scratch/agentAudit/p506.lean` proves, from the hypothesis
`type_of% @Erdos506.erdos_506.variants.large_n`, the answer-free statement
`∀ a : ℕ, ¬ ∀ n : ℕ, 4 ≤ n → IsLeast {…} a`; `#print axioms`: [propext, Classical.choice,
Quot.sound]. Since `large_n` is an upstream placeholder theorem (a literature result, not proved
here), this shows inconsistency between the open statement and the solved one in the same file,
not an unconditional refutation. No result/variant file was written for 506.

## Suggested fix

```lean
def erdos_506.answer : ℕ → ℕ := sorry
theorem erdos_506 (n : ℕ) (hn : 4 ≤ n) : IsLeast {…} (erdos_506.answer n)
```

and the same for `small_n` (domain `4 ≤ n ≤ 393`).
