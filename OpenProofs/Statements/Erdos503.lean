import FormalConjectures.ErdosProblems.«503»

/-!
# Answer-free negation of Erdős 503 (possible misformalization)

Upstream `Erdos503.erdos_503 (n : ℕ) : IsGreatest {...} erdos_503.answer` uses one constant
`erdos_503.answer : ℕ` for every dimension `n`, while the maximum depends on `n` (the same file
records the values `6` for `n = 2` and `8` for `n = 3`). The statement below is the upstream body
with the placeholder replaced by a universally quantified `a`.
-/

open scoped EuclideanGeometry

namespace OpenProofs.Statements.Erdos503

/-- The largest isosceles set in `ℝ^n` does not have the same size for every `n`. -/
theorem erdos_503.no_constant_answer : ∀ a : ℕ, ¬ ∀ n : ℕ,
    IsGreatest {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)} a := by
  sorry

end OpenProofs.Statements.Erdos503
