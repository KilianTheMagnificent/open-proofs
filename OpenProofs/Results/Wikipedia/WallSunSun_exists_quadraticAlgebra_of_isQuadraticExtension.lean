import FormalConjectures.Wikipedia.WallSunSun

/-!
# `Algebra.exists_quadraticAlgebra_of_isQuadraticExtension`

Upstream: `Algebra.exists_quadraticAlgebra_of_isQuadraticExtension` (category textbook), `FormalConjectures/Wikipedia/WallSunSun.lean` line 57.
Proof idea: since `finrank K L = 2`, there is `α : L` with `![1, α]` linearly independent, hence a
basis of `L`. Write `α * α = a • 1 + b • α`; `QuadraticAlgebra.lift` sends `ω ↦ α`, giving a
`K`-algebra map `QuadraticAlgebra K a b →ₐ[K] L`, `⟨x, y⟩ ↦ x • 1 + y • α`. It is injective by
linear independence and surjective because `{1, α}` spans `L`; invert `AlgEquiv.ofBijective`.
-/

open Algebra (IsQuadraticExtension)
open NumberField
open Algebra

namespace OpenProofs.Algebra

variable {d : ℤ} [Fact <| Squarefree d] [Fact <| d ≠ 1]
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem exists_quadraticAlgebra_of_isQuadraticExtension [IsQuadraticExtension K L] :
    ∃ a b, Nonempty (L ≃ₐ[K] QuadraticAlgebra K a b) := by
  have h2 : Module.finrank K L = 2 := IsQuadraticExtension.finrank_eq_two K L
  obtain ⟨α, hα⟩ := exists_linearIndependent_pair_of_one_lt_finrank (R := K) (M := L)
    (by omega) (one_ne_zero (α := L))
  have hspan : Submodule.span K (Set.range ![(1 : L), α]) = ⊤ :=
    hα.span_eq_top_of_card_eq_finrank (by simp [h2])
  have hmem : ∀ x : L, ∃ s t : K, s • (1 : L) + t • α = x := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range ![(1 : L), α]) := hspan ▸ Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] at hx
    exact Submodule.mem_span_pair.mp hx
  obtain ⟨a, b, hab⟩ := hmem (α * α)
  refine ⟨a, b, ⟨(AlgEquiv.ofBijective (QuadraticAlgebra.lift ⟨α, hab.symm⟩) ⟨?_, ?_⟩).symm⟩⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ hz
    simp only [QuadraticAlgebra.lift_apply_apply] at hz
    obtain ⟨rfl, rfl⟩ := LinearIndependent.pair_iff.mp hα x y hz
    rfl
  · intro z
    obtain ⟨s, t, hst⟩ := hmem z
    exact ⟨⟨s, t⟩, by simpa using hst⟩

end OpenProofs.Algebra
