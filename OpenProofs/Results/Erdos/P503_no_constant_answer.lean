import FormalConjectures.ErdosProblems.«503»

/-!
# Erdős 503: no dimension-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos503.erdos_503.no_constant_answer`.

Upstream `Erdos503.erdos_503 (n : ℕ)` asserts that one constant is the largest size of an
isosceles set in `ℝ^n` for every `n`. In `ℝ^0` every set has at most one point, while in `ℝ^1`
a two-point set is (vacuously) isosceles.
-/

open scoped EuclideanGeometry

namespace OpenProofs.Erdos503

theorem erdos_503.no_constant_answer : ∀ a : ℕ, ¬ ∀ n : ℕ,
    IsGreatest {(A.ncard) | (A : Set (ℝ^n)) (hA : A.IsIsosceles)} a := by
  intro a h
  obtain ⟨A, -, hA⟩ := (h 0).1
  have ha : a ≤ 1 := by
    rw [← hA]
    exact Set.ncard_le_one_of_subsingleton _
  have h2 : 2 ∈ {(A.ncard) | (A : Set (ℝ^1)) (hA : A.IsIsosceles)} := by
    refine ⟨{0, EuclideanSpace.single 0 1}, ⟨⟨0, by simp⟩, ?_⟩, ?_⟩
    · intro x hx y hy z hz hxy hyz hxz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        simp_all
    · rw [Set.ncard_pair]
      intro h0
      have := congrArg (fun v => v 0) h0
      simp at this
  have := (h 1).2 h2
  omega

end OpenProofs.Erdos503
