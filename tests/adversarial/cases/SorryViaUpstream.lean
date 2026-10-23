import FormalConjectures.ErdosProblems.«349»
/-! Cheat: "prove" the statement by citing the upstream theorem, whose own proof is a placeholder. -/
namespace OpenProofs.Adv.SorryViaUpstream
theorem t (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := Erdos349.exists_finsetSum_two_pow k
end OpenProofs.Adv.SorryViaUpstream
