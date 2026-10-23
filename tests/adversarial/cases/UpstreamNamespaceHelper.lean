import FormalConjectures.ErdosProblems.«349»
/-! Hygiene violation: a helper declared inside an upstream namespace (not a realized equation
lemma). It must be rejected even though it is harmless here. -/
theorem Erdos349.extra_helper_lemma : True := trivial
namespace OpenProofs.Adv.UpstreamNamespaceHelper
theorem t (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩
end OpenProofs.Adv.UpstreamNamespaceHelper
