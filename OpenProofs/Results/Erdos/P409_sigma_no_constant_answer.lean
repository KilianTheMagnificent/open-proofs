import FormalConjectures.ErdosProblems.«409»

/-!
# Erdős 409, `σ` variant: no `n`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos409.erdos_409.variants.sigma.no_constant_answer`.

Upstream `Erdos409.erdos_409.variants.sigma (n : ℕ) (hn : n > 1) (hterm : ...)` asserts that one
constant is the least number of iterations of `n ↦ σ n - 1` reaching a prime, for every such `n`.
For `n = 2` (prime) the least number is `0`; for `n = 6` the iteration reaches the prime
`σ 6 - 1 = 11`, but `6` itself is not prime, so the least number is not `0`.
-/

open scoped ArithmeticFunction.sigma Nat

namespace OpenProofs.Erdos409

theorem erdos_409.variants.sigma.no_constant_answer :
    ∀ a : ℕ, ¬ ∀ n : ℕ, n > 1 → (∃ i, (σ 1 · - 1)^[i] n |>.Prime) →
      IsLeast { i | (σ 1 · - 1)^[i] n |>.Prime } a := by
  intro a h
  have h2 := (h 2 (by norm_num) ⟨0, by simpa using Nat.prime_two⟩).2
    (show 0 ∈ { i | (σ 1 · - 1)^[i] 2 |>.Prime } by simpa using Nat.prime_two)
  have ha : a = 0 := by simpa using h2
  subst ha
  have hs : σ 1 6 = 12 := by decide
  have h6 := (h 6 (by norm_num) ⟨1, by simp [hs]; norm_num⟩).1
  simp at h6
  norm_num at h6

end OpenProofs.Erdos409
