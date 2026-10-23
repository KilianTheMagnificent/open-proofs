import FormalConjectures.ErdosProblems.«321»

/-!
# Erdős 321: no `N`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos321.erdos_321.no_constant_answer`.

Upstream `Erdos321.erdos_321 (N : ℕ) : R N = erdos_321.answer` says `R` is constant. But
`R 0 = 0` (the only subset of `∅` is empty) and `R 1 ≥ 1` (`{1}` has distinct subset sums `0, 1`).
-/

open Erdos321

namespace OpenProofs.Erdos321

theorem erdos_321.no_constant_answer : ∀ a : ℕ, ¬ ∀ N : ℕ, R N = a := by
  intro a h
  have h0 : R 0 = 0 := by
    unfold R
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro x ⟨A, hA, -, rfl⟩
    have : A = ∅ := by simpa using hA
    simp [this]
  have h1 : 1 ≤ R 1 := by
    unfold R
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro x ⟨A, hA, -, rfl⟩
      simpa using Finset.card_le_card hA
    · refine ⟨{1}, by simp, ?_, by simp⟩
      intro S hS T hT hST
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset,
        Finset.subset_singleton_iff] at hS hT
      rcases hS with rfl | rfl <;> rcases hT with rfl | rfl <;> simp_all
  have := h 0
  have := h 1
  omega

end OpenProofs.Erdos321
