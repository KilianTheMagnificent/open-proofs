import FormalConjectures.ErdosProblems.«828»

/-!
# Erdős 828 at `a = -1` (special case, tier b)

Reference: `OpenProofs.Statements.Erdos828.at_neg_one`, i.e. the open upstream statement
`Erdos828.erdos_828` specialized to `a = -1`. Every prime `p` has `φ p = p - 1`, which divides
`p - 1`; there are infinitely many primes. (Lehmer's question is the converse direction.)
-/

namespace OpenProofs.Erdos828

open scoped Nat

theorem at_neg_one : Set.Infinite {n : ℕ | (φ n : ℤ) ∣ (n : ℤ) + -1} := by
  refine Nat.infinite_setOfPred_prime.mono ?_
  intro p hp
  simp only [Set.mem_ofPred_eq]
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  simp [sub_eq_add_neg]

end OpenProofs.Erdos828
