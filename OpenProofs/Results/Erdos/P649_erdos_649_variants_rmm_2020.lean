import FormalConjectures.ErdosProblems.«649»

/-!
# `Erdos649.erdos_649.variants.rmm_2020`

Upstream: `Erdos649.erdos_649.variants.rmm_2020` (category textbook), `FormalConjectures/ErdosProblems/649.lean` line 123.
Proof idea: if `P(n) P(n+1) = 2p` with `p` an odd prime, then one of `n`, `n+1` is a power
`2^k` and `p` is the greatest prime factor of `2^k - 1` or `2^k + 1`. If `q > p` is a prime with
the same multiplicative order of `2` as `p`, then `q` divides that number too, which is
impossible. Such pairs exist for every prime `r ≥ 7`: with `x = 2^((r-1)/2)` the Aurifeuillian
factorization `2^(2r) + 1 = 4x^4 + 1 = (2x^2 + 2x + 1)(2x^2 - 2x + 1)` has coprime factors,
`25 ∤ 2^(2r) + 1`, so each factor has a prime divisor other than `5`, and every such prime has
order exactly `4r`, hence is larger than `r`.
-/

open Erdos649

namespace OpenProofs.Erdos649

/-- If two odd primes `p < q` have the same powers of `2` equal to one, then `p` is never
`P(n)` with `P(n+1) = 2` or vice versa. -/
theorem rmm2020_good_of_same_order (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hpq : p < q) (hord : ∀ m : ℕ, (2 : ZMod p) ^ m = 1 ↔ (2 : ZMod q) ^ m = 1) (n : ℕ) :
    n.maxPrimeFac * (n + 1).maxPrimeFac ≠ 2 * p := by
  have := Fact.mk hp
  have := Fact.mk hq
  intro h
  have hp1 := hp.one_lt
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp at h; omega
    · simp [Nat.prime_two.maxPrimeFac_eq_self] at h; omega
  have ha : (n.maxPrimeFac).Prime := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hb : ((n + 1).maxPrimeFac).Prime := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hadvd : n.maxPrimeFac ∣ 2 * p := ⟨_, h.symm⟩
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h1
    have : ((2 : ℕ) : ZMod p) = 0 := by
      have e : ((2 : ℕ) : ZMod p) = 1 - (-1) := by push_cast; ring
      rw [e, h1]; ring
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rcases (Nat.Prime.dvd_mul ha).mp hadvd with h2 | h2
  · -- `P(n) = 2`, so `n = 2^k` and `P(2^k + 1) = p`.
    have hP2 : n.maxPrimeFac = 2 := (Nat.prime_dvd_prime_iff_eq ha Nat.prime_two).mp h2
    have hPp : (n + 1).maxPrimeFac = p := by rw [hP2] at h; omega
    obtain ⟨k, hk⟩ : ∃ k, n = 2 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
        (fun {d} hd hdd ↦
          le_antisymm (hP2 ▸ Nat.le_maxPrimeFac (by omega) hd hdd) hd.two_le)⟩
    have hpd : p ∣ n + 1 := hPp ▸ Nat.maxPrimeFac_dvd
    have hp' : (2 : ZMod p) ^ k = -1 := by
      have : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
      rw [hk] at this; push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    have hp'' : (2 : ZMod p) ^ (2 * k) = 1 := by rw [pow_mul', hp']; norm_num
    have hq'' := (hord _).mp hp''
    rw [pow_mul', sq] at hq''
    rcases mul_self_eq_one_iff.mp hq'' with hq1 | hq1
    · exact hneg (hp' ▸ (hord k).mpr hq1)
    · have : ((n + 1 : ℕ) : ZMod q) = 0 := by rw [hk]; push_cast; rw [hq1]; ring
      rw [ZMod.natCast_eq_zero_iff] at this
      have := Nat.le_maxPrimeFac (by omega) hq this
      omega
  · -- `P(n) = p`, so `P(n + 1) = 2`, `n + 1 = 2^k` and `p ∣ 2^k - 1`.
    have hPp : n.maxPrimeFac = p := (Nat.prime_dvd_prime_iff_eq ha hp).mp h2
    have hP2 : (n + 1).maxPrimeFac = 2 := by
      rw [hPp] at h
      exact Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_comm 2 p))
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = 2 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
        (fun {d} hd hdd ↦
          le_antisymm (hP2 ▸ Nat.le_maxPrimeFac (by omega) hd hdd) hd.two_le)⟩
    have hpd : p ∣ n := hPp ▸ Nat.maxPrimeFac_dvd
    have hp' : (2 : ZMod p) ^ k = 1 := by
      have h0 : ((n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
      have : ((n + 1 : ℕ) : ZMod p) = ((2 ^ k : ℕ) : ZMod p) := by rw [hk]
      push_cast at this; rw [h0] at this; rw [← this]; ring
    have hq' := (hord k).mp hp'
    have : ((n : ℕ) : ZMod q) = 0 := by
      have e : ((n + 1 : ℕ) : ZMod q) = ((2 ^ k : ℕ) : ZMod q) := by rw [hk]
      push_cast at e; rw [hq'] at e
      linear_combination e
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_maxPrimeFac (by omega) hq this
    omega

/-- Every prime divisor `t ≠ 5` of `2^(2r) + 1`, `r` a prime, is odd and has order `4r`. -/
theorem rmm2020_orderOf_eq (r t : ℕ) (hr : r.Prime) (ht : t.Prime)
    (hdvd : t ∣ 2 ^ (2 * r) + 1) (ht5 : t ≠ 5) :
    t ≠ 2 ∧ orderOf (2 : ZMod t) = 4 * r := by
  have := Fact.mk ht
  have ht2 : t ≠ 2 := by
    rintro rfl
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by have := hr.pos; omega))).mp hdvd
    omega
  refine ⟨ht2, ?_⟩
  have h1 : (2 : ZMod t) ^ (2 * r) = -1 := by
    have : ((2 ^ (2 * r) + 1 : ℕ) : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hne : (-1 : ZMod t) ≠ 1 := by
    intro h
    have : ((2 : ℕ) : ZMod t) = 0 := by
      have e : ((2 : ℕ) : ZMod t) = 1 - (-1) := by push_cast; ring
      rw [e, h]; ring
    rw [ZMod.natCast_eq_zero_iff] at this
    exact ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp this)
  have h4 : (2 : ZMod t) ^ (4 * r) = 1 := by
    rw [show 4 * r = 2 * r * 2 by ring, pow_mul, h1]; norm_num
  have hdvd4 : orderOf (2 : ZMod t) ∣ 4 * r := orderOf_dvd_of_pow_eq_one h4
  have hndvd : ¬ orderOf (2 : ZMod t) ∣ 2 * r := by
    intro h
    rw [orderOf_dvd_iff_pow_eq_one, h1] at h
    exact hne h
  rcases Nat.coprime_or_dvd_of_prime hr (orderOf (2 : ZMod t)) with hc | hro
  · exfalso
    have h4' : orderOf (2 : ZMod t) ∣ 4 := Nat.Coprime.dvd_of_dvd_mul_right hc.symm hdvd4
    have h16 : (2 : ZMod t) ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp h4'
    have h15 : ((15 : ℕ) : ZMod t) = 0 := by
      have e : ((15 : ℕ) : ZMod t) = 2 ^ 4 - 1 := by push_cast; norm_num
      rw [e, h16]; ring
    rw [ZMod.natCast_eq_zero_iff] at h15
    have ht15 : t ≤ 15 := Nat.le_of_dvd (by norm_num) h15
    have hmod : (2 ^ (2 * r) + 1) % 3 = 2 := by
      rw [pow_mul, Nat.add_mod, Nat.pow_mod]; norm_num
    interval_cases t <;> first | omega | norm_num at ht
  · obtain ⟨j, hj⟩ := hro
    have hj4 : j ∣ 4 := by
      rw [hj, mul_comm 4 r] at hdvd4
      exact (Nat.mul_dvd_mul_iff_left hr.pos).mp hdvd4
    have hj4' : j ≤ 4 := Nat.le_of_dvd (by norm_num) hj4
    rw [hj] at hndvd ⊢
    interval_cases j
    · norm_num at hj4
    · exact absurd (Dvd.intro_left 2 (by ring)) hndvd
    · exact absurd (by rw [mul_comm]) hndvd
    · norm_num at hj4
    · ring

/-- A number `X > 5` not divisible by `25` has a prime factor other than `5`. -/
theorem rmm2020_exists_prime_ne_five (X : ℕ) (hX : 5 < X) (h25 : ¬ 25 ∣ X) :
    ∃ t, t.Prime ∧ t ∣ X ∧ t ≠ 5 := by
  by_cases h5 : 5 ∣ X
  · obtain ⟨Y, rfl⟩ := h5
    have hY5 : ¬ 5 ∣ Y := by
      rintro ⟨Z, rfl⟩; exact h25 ⟨Z, by ring⟩
    have hY1 : Y ≠ 1 := by rintro rfl; omega
    refine ⟨Y.minFac, Nat.minFac_prime hY1, dvd_mul_of_dvd_right (Nat.minFac_dvd Y) 5, ?_⟩
    intro h; exact hY5 (h ▸ Nat.minFac_dvd Y)
  · have hX1 : X ≠ 1 := by omega
    refine ⟨X.minFac, Nat.minFac_prime hX1, Nat.minFac_dvd X, ?_⟩
    intro h; exact h5 (h ▸ Nat.minFac_dvd X)

/-- `25 ∤ 2^(2r) + 1` for a prime `r > 5`. -/
theorem rmm2020_not_25_dvd (r : ℕ) (hr : r.Prime) (hr5 : 5 < r) : ¬ 25 ∣ 2 ^ (2 * r) + 1 := by
  have hr2 : r % 2 = 1 := by
    by_contra h0
    rcases hr.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h | h <;> omega
  have hr5' : r % 5 ≠ 0 := by
    intro h0
    rcases hr.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  have hmod : 2 ^ (2 * r) % 25 = 4 ^ (r % 10) % 25 := by
    rw [pow_mul]
    conv_lhs => rw [← Nat.div_add_mod r 10, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h10 : r % 10 < 10 := Nat.mod_lt _ (by norm_num)
  intro h
  have h0 : (2 ^ (2 * r) + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd h
  interval_cases hh : r % 10 <;> omega

/-- Two primes of the same order `4r` give a member `p > r` of the set. -/
theorem rmm2020_mem (p q r a : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hpq : p < q)
    (hop : orderOf (2 : ZMod p) = 4 * r) (hoq : orderOf (2 : ZMod q) = 4 * r) (ha : a < r) :
    p.Prime ∧ Odd p ∧ (∀ n : ℕ, n.maxPrimeFac * (n + 1).maxPrimeFac ≠ 2 * p) ∧ a < p := by
  refine ⟨hp, hp.odd_of_ne_two hp2, rmm2020_good_of_same_order p q hp hq hp2 hpq ?_, ?_⟩
  · intro m
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one, hop, hoq]
  · have := Fact.mk hp
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hd := ZMod.orderOf_dvd_card_sub_one h2
    rw [hop] at hd
    have := Nat.le_of_dvd (by have := hp.two_le; omega) hd
    omega

theorem erdos_649.variants.rmm_2020 :
    {p : ℕ | p.Prime ∧ Odd p ∧
      ∀ n : ℕ, n.maxPrimeFac * (n + 1).maxPrimeFac ≠ 2 * p}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨r, hra, hr⟩ := Nat.exists_infinite_primes (a + 7)
  have hr2 : r ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hk3 : 3 ≤ k := by omega
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ k = y + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hy7 : 7 ≤ y := by
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  have hN : 2 ^ (2 * r) + 1 = (2 * (y + 1) ^ 2 + 2 * (y + 1) + 1) * (2 * (y + 1) * y + 1) := by
    have : 2 ^ (2 * r) = 4 * (2 ^ k) ^ 4 := by rw [hk]; ring
    rw [this, hy]; ring
  have hAB : 2 * (y + 1) ^ 2 + 2 * (y + 1) + 1 = (2 * (y + 1) * y + 1) + 2 ^ (k + 2) := by
    rw [pow_add, hy]; ring
  have hB : 5 < 2 * (y + 1) * y + 1 := by nlinarith
  have hA : 5 < 2 * (y + 1) ^ 2 + 2 * (y + 1) + 1 := by nlinarith
  have h25 := rmm2020_not_25_dvd r hr (by omega)
  obtain ⟨t1, ht1, ht1A, ht15⟩ := rmm2020_exists_prime_ne_five _ hA
    (fun h ↦ h25 (hN ▸ dvd_mul_of_dvd_left h _))
  obtain ⟨t2, ht2, ht2B, ht25⟩ := rmm2020_exists_prime_ne_five _ hB
    (fun h ↦ h25 (hN ▸ dvd_mul_of_dvd_right h _))
  obtain ⟨ht12, ho1⟩ := rmm2020_orderOf_eq r t1 hr ht1 (hN ▸ dvd_mul_of_dvd_left ht1A _) ht15
  obtain ⟨ht22, ho2⟩ := rmm2020_orderOf_eq r t2 hr ht2 (hN ▸ dvd_mul_of_dvd_right ht2B _) ht25
  have hne : t1 ≠ t2 := by
    rintro rfl
    have h4 : t1 ∣ 2 ^ (k + 2) := (Nat.dvd_add_right ht2B).mp (hAB ▸ ht1A)
    exact ht12 ((Nat.prime_dvd_prime_iff_eq ht1 Nat.prime_two).mp (ht1.dvd_of_dvd_pow h4))
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨h1, h2, h3, h4⟩ := rmm2020_mem t1 t2 r a ht1 ht2 ht12 h ho1 ho2 (by omega)
    exact ⟨t1, ⟨h1, h2, h3⟩, h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := rmm2020_mem t2 t1 r a ht2 ht1 ht22 h ho2 ho1 (by omega)
    exact ⟨t2, ⟨h1, h2, h3⟩, h4⟩

end OpenProofs.Erdos649
