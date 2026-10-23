# Possible misformalization: Erdős 409 (`Erdos409.erdos_409.parts.i`, `Erdos409.erdos_409.variants.sigma`)

Status: draft for the owner. Nothing has been filed or sent.

- Upstream: google-deepmind/formal-conjectures at `96343eeb5990ff13735e728cd0195eff0156a3bb`, `FormalConjectures/ErdosProblems/409.lean`
- Informal source: https://www.erdosproblems.com/409
- Pattern: a `question value` statement whose `answer` placeholder is a single constant, although the quantity asked for depends on a parameter that the theorem quantifies over. Whatever value the placeholder is given, the statement is false.

## Upstream Lean statement

```lean
def erdos_409.parts.i.answer : ℕ := sorry
theorem erdos_409.parts.i (n : ℕ) (hn : 0 < n) :
    IsLeast { i | (φ · + 1)^[i] n |>.Prime } erdos_409.parts.i.answer

def erdos_409.variants.sigma.answer : ℕ := sorry
theorem erdos_409.variants.sigma (n : ℕ) (hn : n > 1)
    (hterm : ∃ i, (σ 1 · - 1)^[i] n |>.Prime) :
    IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } erdos_409.variants.sigma.answer
```

## Informal statement

"How many iterations of n ↦ φ(n) + 1 are needed before a prime is reached?" (and the same for
n ↦ σ(n) − 1, assuming a prime is reached). The number of iterations is a function of the
starting value `n`.

## Why they differ

Each `answer : ℕ` is a single number for all starting values. The least number of iterations is
`0` exactly when `n` is prime: for `parts.i`, `n = 2` gives `0` and `n = 1` does not (1 is not
prime); for `variants.sigma`, `n = 2` gives `0` and `n = 6` does not (6 is not prime, and
`σ(6) - 1 = 11` is prime, so `hterm` holds). The file's own asymptotic variants
(`parts.i.isTheta`, `sigma_isTheta`, …) correctly treat the count as a function `c : ℕ → ℕ`.

## Lean evidence

- Variant statements: `OpenProofs/Statements/Erdos409.lean`,
  `OpenProofs.Statements.Erdos409.erdos_409.parts.i.no_constant_answer :
   ∀ a : ℕ, ¬ ∀ n : ℕ, 0 < n → IsLeast { i | (φ · + 1)^[i] n |>.Prime } a` and
  `OpenProofs.Statements.Erdos409.erdos_409.variants.sigma.no_constant_answer` (same shape).
- Proofs: `OpenProofs/Results/Erdos/P409_parts_i_no_constant_answer.lean`,
  `OpenProofs/Results/Erdos/P409_sigma_no_constant_answer.lean`. `#print axioms`: [propext, Classical.choice, Quot.sound] for both
  (scratch copy `work/scratch/agentAudit/p409.lean`).
- Checker verdict: PASS on all five layers (coordinator run, 2026-10-23; see `ledger/LEDGER.md`).
- The literal negation `¬ type_of% @Erdos409.erdos_409.parts.i` follows from the answer-free form in one line (`fun h => erdos_409.parts.i.no_constant_answer _ h`, checked in scratch), but it mentions `erdos_409.parts.i.answer`, whose body is a placeholder, so its axiom list contains the placeholder axiom and this project's checker would reject it. The answer-free form is strictly stronger and is what was proved.

## Suggested fix

Make the answers functions of `n`, e.g. `def erdos_409.parts.i.answer : ℕ → ℕ := sorry` and
`IsLeast {…} (erdos_409.parts.i.answer n)`; same for `variants.sigma`. (As stated, "find a closed
formula for the iteration count" is probably not what is intended either; the asymptotic variants
may be the better primary formalization.)

## Related, not refuted: `erdos_409.parts.iii`

`erdos_409.parts.iii (p : ℕ) (h : p.Prime) : {n | ∃ i, (φ · + 1)^[i] n = p}.HasDensity
erdos_409.parts.iii.answer` has the same shape (one density for every prime `p`). It is not
refutable by a short argument, but it forces the placeholder to be `0`: the sets for different
primes are pairwise disjoint (the iteration is fixed at a prime, so each `n` reaches exactly one
prime) and the set for `p = 2` is `{0, 1, 2}` (finite, density 0). So, as stated, the theorem is
equivalent to "every such set has density 0", which is a different question from "what is the
density for a fixed prime p". Suggested fix: `answer : ℕ → ℝ` and `HasDensity (answer p)`.
