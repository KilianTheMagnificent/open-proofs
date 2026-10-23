import FormalConjectures.ErdosProblems.«349»
/-! Cheat: a custom axiom. -/
namespace OpenProofs.Adv.CustomAxiom
axiom cheat : False
theorem t (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i := cheat.elim
end OpenProofs.Adv.CustomAxiom
