import FormalConjectures.ErdosProblems.«692»

/-!
# Answer-free negation of Erdős 692 (ii) (possible misformalization)

Upstream `Erdos692.erdos_692.parts.ii (n : ℕ)` asserts that `δ₁(n, m)` attains its maximum over
`m > n + 1` at one constant `m = erdos_692.parts.ii.answer`, for every `n`. The statement below is
the upstream body with the placeholder replaced by a universally quantified `m₀`.
-/

open Erdos692

namespace OpenProofs.Statements.Erdos692

/-- No single `m₀` is a maximiser of `m ↦ δ₁(n, m)` (over `m > n + 1`) for every `n`. -/
theorem erdos_692.parts.ii.no_constant_answer :
    ∀ m₀ : ℕ, ¬ ∀ (n : ℕ), ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ n '' Set.Ioi (n + 1)) (δ n m₀) := by
  sorry

end OpenProofs.Statements.Erdos692
