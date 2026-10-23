import FormalConjectures.ErdosProblems.«409»

/-!
# Answer-free negations of Erdős 409 (possible misformalization)

Upstream `Erdos409.erdos_409.parts.i (n : ℕ) (hn : 0 < n)` and `Erdos409.erdos_409.variants.sigma`
assert that one constant `answer : ℕ` is the least number of iterations for every starting value
`n`, while that number depends on `n` (it is `0` exactly when `n` is prime). The statements below
are the upstream bodies with the placeholders replaced by a universally quantified `a`.
-/

open scoped ArithmeticFunction.sigma Nat

namespace OpenProofs.Statements.Erdos409

/-- The number of iterations of `n ↦ φ n + 1` needed to reach a prime is not constant. -/
theorem erdos_409.parts.i.no_constant_answer :
    ∀ a : ℕ, ¬ ∀ n : ℕ, 0 < n → IsLeast { i | (φ · + 1)^[i] n |>.Prime } a := by
  sorry

/-- The number of iterations of `n ↦ σ n - 1` needed to reach a prime is not constant. -/
theorem erdos_409.variants.sigma.no_constant_answer :
    ∀ a : ℕ, ¬ ∀ n : ℕ, n > 1 → (∃ i, (σ 1 · - 1)^[i] n |>.Prime) →
      IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } a := by
  sorry

end OpenProofs.Statements.Erdos409
