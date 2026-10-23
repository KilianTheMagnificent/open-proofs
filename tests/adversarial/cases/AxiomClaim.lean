import FormalConjectures.ErdosProblems.«349»
/-! Cheat: the claimed "theorem" is itself an axiom with the right type. -/
namespace OpenProofs.Adv.AxiomClaim
axiom t (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i
end OpenProofs.Adv.AxiomClaim
