import FormalConjectures.ErdosProblems.«319»

/-!
# Answer-free negation of Erdős 319 (possible misformalization)

Upstream `Erdos319.erdos_319 (N : ℕ) : IsGreatest {...} erdos_319.answer` uses one constant
`erdos_319.answer : ℕ` for every `N`, while the maximum depends on `N`. The statement below is the
upstream body with the placeholder `erdos_319.answer` replaced by a universally quantified `a`.
-/

namespace OpenProofs.Statements.Erdos319

open scoped Finset in
/-- No single natural number is the maximum in `erdos_319` for every `N`. -/
theorem erdos_319.no_constant_answer : ∀ a : ℕ, ¬ ∀ N : ℕ, IsGreatest
    { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) } a := by
  sorry

end OpenProofs.Statements.Erdos319
