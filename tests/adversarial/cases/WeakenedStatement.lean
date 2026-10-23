import FormalConjectures.ErdosProblems.«349»
/-! Cheat: a vacuous extra hypothesis makes the statement trivial. -/
namespace OpenProofs.Adv.WeakenedStatement
theorem t (k : ℕ) (h : k < 0) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  absurd h (Nat.not_lt_zero k)
end OpenProofs.Adv.WeakenedStatement
