import FormalConjectures.ErdosProblems.«828»

/-!
# Erdős 828 at `a = 0` (special case, tier b)

Reference: `OpenProofs.Statements.Erdos828.at_zero`, i.e. the open upstream statement
`Erdos828.erdos_828` specialized to `a = 0`. Every power of two `2 ^ (k + 1)` has
`φ (2 ^ (k + 1)) = 2 ^ k`, which divides it. A well-known easy case; it says nothing about
general `a`.
-/

namespace OpenProofs.Erdos828

open scoped Nat

theorem at_zero : Set.Infinite {n : ℕ | (φ n : ℤ) ∣ (n : ℤ) + 0} := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 1)) ?_ ?_
  · intro a b h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  · intro k
    simp only [Set.mem_ofPred_eq, add_zero]
    rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
    norm_cast
    exact ⟨2, by simp [pow_succ]⟩

end OpenProofs.Erdos828
