import FormalConjectures.ErdosProblems.«12»

/-!
# `Erdos12.isGood_example`

Upstream: `Erdos12.isGood_example` (category textbook), `FormalConjectures/ErdosProblems/12.lean` line 45.
Proof idea: the set is the image of the primes `p ≡ 3 [MOD 4]` under the injective map
`p ↦ p ^ 2`, and there are infinitely many such primes (Dirichlet, in Mathlib). For the
divisibility condition, if `p ^ 2 ∣ q ^ 2 + r ^ 2` with `p < q`, `p < r` primes, then
`p ∤ r` and `q ^ 2 = -r ^ 2` in `ZMod p`, so `-1` is a square mod `p`, contradicting
`p % 4 = 3`. Hence the hypothesis is never met and the condition holds vacuously.
-/

open Filter Set
open Erdos12

namespace OpenProofs.Erdos12

theorem isGood_example :
    IsGood {p ^ 2 | (p : ℕ) (_ : p ≡ 3 [MOD 4]) (_ : p.Prime)} := by
  refine ⟨?_, ?_⟩
  · have hset : {p ^ 2 | (p : ℕ) (_ : p ≡ 3 [MOD 4]) (_ : p.Prime)} =
        (fun p : ℕ => p ^ 2) '' {p : ℕ | p.Prime ∧ p ≡ 3 [MOD 4]} := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨p, h3, hp, rfl⟩
        exact ⟨p, ⟨hp, h3⟩, rfl⟩
      · rintro ⟨p, ⟨hp, h3⟩, rfl⟩
        exact ⟨p, h3, hp, rfl⟩
    rw [hset]
    refine Set.Infinite.image ?_ (Nat.infinite_setOfPred_prime_and_modEq (by norm_num) (by norm_num))
    intro x _ y _ hxy
    exact Nat.pow_left_injective (by norm_num) hxy
  · rintro a ⟨p, hp3, hp, rfl⟩ b ⟨q, hq3, hq, rfl⟩ c ⟨r, hr3, hr, rfl⟩ hdvd _ hac
    exfalso
    have hpr : p < r := by
      by_contra h
      rw [not_lt] at h
      have := Nat.pow_le_pow_left h 2
      omega
    have : Fact p.Prime := ⟨hp⟩
    have hdvd' : p ∣ q ^ 2 + r ^ 2 := (Dvd.intro_left _ (pow_two p).symm).trans hdvd
    have hrne : ((r : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hpr'
      rcases (Nat.Prime.eq_one_or_self_of_dvd hr p hpr') with h | h
      · exact hp.one_lt.ne' h
      · omega
    have hsq : ((q : ℕ) : ZMod p) ^ 2 = -((r : ℕ) : ZMod p) ^ 2 := by
      have h0 : ((q ^ 2 + r ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd'
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    have := ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hrne hsq
    exact this hp3

end OpenProofs.Erdos12
