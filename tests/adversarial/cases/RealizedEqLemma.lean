import FormalConjectures.ErdosProblems.«349»
/-! Positive control: unfolding an upstream definition with `simp only` realizes its equation
lemma `Erdos349.IsGoodPair.eq_1` in this module; that is allowed. -/
namespace OpenProofs.Adv.RealizedEqLemma
theorem unfold_helper (t α : ℝ) :
    Erdos349.IsGoodPair t α ↔ IsAddComplete (Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋)) := by
  simp only [Erdos349.IsGoodPair]
theorem t (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩
end OpenProofs.Adv.RealizedEqLemma
