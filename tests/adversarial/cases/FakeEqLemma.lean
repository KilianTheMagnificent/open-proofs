import FormalConjectures.ErdosProblems.«349»
/-! Hygiene violation: a hand-written theorem whose name *looks like* a realized equation lemma
(`eq_` prefix) under an upstream definition's namespace. Lean reserves `eq_<digits>`, `eq_def`
and `eq_unfold`, so this uses another `eq_` name; the checker must reject it. -/
theorem Erdos349.IsGoodPair.eq_helper : True := trivial
namespace OpenProofs.Adv.FakeEqLemma
theorem t (k : ℕ) : ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩
end OpenProofs.Adv.FakeEqLemma
