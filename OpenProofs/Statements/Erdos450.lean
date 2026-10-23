import FormalConjectures.ErdosProblems.«450»

/-!
# Answer-free negation of Erdős 450 (possible misformalization)

Upstream `Erdos450.erdos_450 (ε : ℝ) (hε : 0 < ε) (n : ℕ) : windowThreshold ε n = erdos_450.answer`
uses one constant `erdos_450.answer : ℕ∞` for every `ε` and `n`, while the problem asks for
`y(ε, n)`. The statement below is the upstream body with the placeholder replaced by a universally
quantified `a`.
-/

open Erdos450

namespace OpenProofs.Statements.Erdos450

/-- `windowThreshold ε n` is not constant in `ε` and `n`. -/
theorem erdos_450.no_constant_answer :
    ∀ a : ℕ∞, ¬ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, windowThreshold ε n = a := by
  sorry

end OpenProofs.Statements.Erdos450
