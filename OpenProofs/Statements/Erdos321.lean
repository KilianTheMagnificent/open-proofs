import FormalConjectures.ErdosProblems.«321»

/-!
# Answer-free negation of Erdős 321 (possible misformalization)

Upstream `Erdos321.erdos_321 (N : ℕ) : R N = erdos_321.answer` uses one constant
`erdos_321.answer : ℕ` for every `N`, while `R N` depends on `N` (`R 0 = 0`, `R 1 = 1`). The
statement below is the upstream body with the placeholder replaced by a universally quantified `a`.
-/

open Erdos321

namespace OpenProofs.Statements.Erdos321

/-- `R` is not constant. -/
theorem erdos_321.no_constant_answer : ∀ a : ℕ, ¬ ∀ N : ℕ, R N = a := by
  sorry

end OpenProofs.Statements.Erdos321
