import FormalConjectures.ErdosProblems.«361»

/-!
# Answer-free negation of Erdős 361 (possible misformalization)

Upstream `Erdos361.erdos_361 (c : ℝ) (hc : 0 < c) : subsetSumAvoidanceNumber c = erdos_361.answer`
uses one function `erdos_361.answer : ℕ → ℕ` of `n` alone for every `c > 0`, while the quantity
depends on `c`. The statement below is the upstream body with the placeholder replaced by a
universally quantified `a`.
-/

open Erdos361

namespace OpenProofs.Statements.Erdos361

/-- `subsetSumAvoidanceNumber c` is not the same function for every `c > 0`. -/
theorem erdos_361.no_constant_answer :
    ∀ a : ℕ → ℕ, ¬ ∀ c : ℝ, 0 < c → subsetSumAvoidanceNumber c = a := by
  sorry

end OpenProofs.Statements.Erdos361
