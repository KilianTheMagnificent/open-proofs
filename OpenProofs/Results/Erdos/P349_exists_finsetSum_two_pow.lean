import FormalConjectures.ErdosProblems.«349»

/-!
# Erdős 349: `exists_finsetSum_two_pow`

Upstream: `Erdos349.exists_finsetSum_two_pow` (category `textbook`).
Every natural number is a sum of distinct powers of two (binary expansion).
-/

namespace OpenProofs.Erdos349

theorem exists_finsetSum_two_pow (k : ℕ) :
    ∃ E : Finset ℕ, k = ∑ i ∈ E, 2 ^ i :=
  ⟨k.bitIndices.toFinset, (Finset.sum_toFinset_bitIndices_two_pow k).symm⟩

end OpenProofs.Erdos349
