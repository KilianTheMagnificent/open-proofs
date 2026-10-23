import FormalConjectures.ErdosProblems.«292»

/-!
# Erdős 292: `erdos_292.variants.prime_pow`

Upstream: `Erdos292.erdos_292.variants.prime_pow`. Suppose `n = p ^ k` (with `p` prime, `k ≥ 1`)
lies in `A`, witnessed by `S ⊆ [1, n]` with `n ∈ S` and `∑ 1/m = 1`. Write the sum as
`1/p^k + r`, where `r` sums over `S \ {n}`. Every `m ∈ S \ {n}` satisfies `1 ≤ m < p^k`, so
`p^k ∤ m` and `v_p(1/m) > -k`; by the ultrametric inequality `v_p(r) > -k` (also when `r = 0`).
Then `1/p^k = 1 + (-r)` would have valuation `≥ min(v_p(1), v_p(r)) > -k`, contradicting
`v_p(1/p^k) = -k`.
-/

open Erdos292

namespace OpenProofs.Erdos292

/-- If every term of a finite sum of rationals has `p`-adic valuation `> c` for some `c < 0`,
then so does the sum (the zero sum has valuation `0 > c`). -/
theorem helper_prime_pow_lt_padicValRat_sum (p : ℕ) [Fact p.Prime] (c : ℤ) (hc : c < 0)
    (F : ℕ → ℚ) (S : Finset ℕ) (h : ∀ i ∈ S, c < padicValRat p (F i)) :
    c < padicValRat p (∑ i ∈ S, F i) := by
  induction S using Finset.induction_on with
  | empty => simpa using hc
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    by_cases h0 : F a + ∑ i ∈ S, F i = 0
    · rw [h0, padicValRat.zero]
      exact hc
    · exact lt_of_lt_of_le (lt_min (h a (Finset.mem_insert_self a S))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
        (padicValRat.min_le_padicValRat_add h0)

theorem erdos_292.variants.prime_pow : ∀ n ∈ A, ¬ IsPrimePow n := by
  rintro n ⟨S, hSsub, hnS, hsum⟩ hpp
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have : Fact p.Prime := ⟨hp⟩
  set r := ∑ m ∈ S.erase (p ^ k), (1 : ℚ) / m with hr
  have hsplit : (1 : ℚ) / ((p ^ k : ℕ) : ℚ) + r = 1 := by
    rw [hr, Finset.add_sum_erase S (fun m : ℕ => (1 : ℚ) / m) hnS]
    exact hsum
  have hvn : padicValRat p ((1 : ℚ) / ((p ^ k : ℕ) : ℚ)) = -k := by
    rw [one_div, Nat.cast_pow, padicValRat.self_pow_inv]
  have hvr : -(k : ℤ) < padicValRat p r := by
    apply helper_prime_pow_lt_padicValRat_sum p _ (by omega)
    intro m hm
    obtain ⟨hmn, hmS⟩ := Finset.mem_erase.mp hm
    have hmI := Finset.mem_Icc.mp (hSsub hmS)
    rw [one_div, padicValRat.inv, padicValRat.of_nat, neg_lt_neg_iff, Nat.cast_lt]
    by_contra hle
    have hdvd : p ^ k ∣ m := (Nat.pow_dvd_pow p (not_lt.mp hle)).trans pow_padicValNat_dvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have heq : (1 : ℚ) + -r = 1 / ((p ^ k : ℕ) : ℚ) := by linarith
  have hne : (1 : ℚ) + -r ≠ 0 := by
    rw [heq]
    have : (0 : ℚ) < ((p ^ k : ℕ) : ℚ) := by exact_mod_cast pow_pos hp.pos k
    positivity
  have hmin := padicValRat.min_le_padicValRat_add (p := p) hne
  rw [heq, hvn, padicValRat.one, padicValRat.neg] at hmin
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  rcases min_le_iff.mp hmin with h | h <;> omega

end OpenProofs.Erdos292
