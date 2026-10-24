import FormalConjectures.ErdosProblems.«828»

/-!
# `Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3`

Upstream: `Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3` (category textbook), `FormalConjectures/ErdosProblems/828.lean` line 53.
Proof idea: `←` is a direct totient computation, `φ (2 ^ a * 3 ^ b) = 2 ^ (a - 1) * φ (3 ^ b)`.
For `→` with `n ≥ 2`: `φ n` is even for `n > 2`, so `n` is even; write `n = 2 ^ a * m` with `m`
odd and `a ≥ 1`, then `φ n = 2 ^ (a - 1) * φ m` and cancelling gives `φ m ∣ 2 * m`. If `m > 1`,
take an odd prime `p ∣ m` and write `m = p ^ e * r` with `p ∤ r`. If `r > 1` then `p - 1` and
`φ r` are both even, so `4 ∣ φ m ∣ 2 * m`, contradicting `m` odd. So `m = p ^ e` and
`p - 1 ∣ 2 * p = 2 * (p - 1) + 2`, whence `p - 1 ∣ 2` and `p = 3`.
-/

open scoped Nat
open Erdos828

namespace OpenProofs.Erdos828

/-- If `m` is odd and `φ m ∣ 2 * m`, then `m` is a power of three. -/
theorem odd_totient_dvd_two_mul_pow_three {m : ℕ} (hm : Odd m) (h : φ m ∣ 2 * m) :
    ∃ b, m = 3 ^ b := by
  by_cases hm1 : m = 1
  · exact ⟨0, by simp [hm1]⟩
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set p := m.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hm1
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpm
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hpm)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨e, r, hpr, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.one_lt.ne'
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      simp only [pow_zero, one_mul] at hmr
      exact absurd (hmr ▸ hpm) hpr
    · exact he
  have hcop : Nat.Coprime (p ^ e) r :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr)
  have htot : φ m = p ^ (e - 1) * (p - 1) * φ r := by
    rw [hmr, Nat.totient_mul hcop, Nat.totient_prime_pow hp he]
  have hr0 : r ≠ 0 := by rintro rfl; simp at hmr; exact hm0 hmr
  by_cases hr1 : r = 1
  · subst hr1
    refine ⟨e, ?_⟩
    rw [Nat.totient_one, mul_one] at htot
    rw [htot, hmr, mul_one] at h
    have hpe : p ^ e = p ^ (e - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hpe, show 2 * (p ^ (e - 1) * p) = p ^ (e - 1) * (2 * p) by ring] at h
    have hpos : 0 < p ^ (e - 1) := pow_pos hp.pos _
    have h1 : p - 1 ∣ 2 * p := (Nat.mul_dvd_mul_iff_left hpos).mp h
    have h2 : 2 * p = 2 * (p - 1) + 2 := by have := hp.two_le; omega
    rw [h2] at h1
    have h3 : p - 1 ∣ 2 := (Nat.dvd_add_right (dvd_mul_left _ _)).mp h1
    have h4 : p - 1 ≤ 2 := Nat.le_of_dvd two_pos h3
    have h5 : p = 3 := by
      have := hp.two_le
      obtain ⟨k, hk⟩ := hpodd
      omega
    rw [hmr, h5, mul_one]
  · exfalso
    have hrodd : Odd r := (Nat.odd_mul.mp (hmr ▸ hm)).2
    have hr3 : 2 < r := by
      obtain ⟨k, hk⟩ := hrodd
      omega
    obtain ⟨u, hu⟩ := Nat.totient_even hr3
    obtain ⟨v, hv⟩ : Even (p - 1) := by
      obtain ⟨k, hk⟩ := hpodd
      exact ⟨k, by omega⟩
    have h4 : 4 ∣ φ m := ⟨p ^ (e - 1) * v * u, by rw [htot, hu, hv]; ring⟩
    have h4' : 4 ∣ 2 * m := h4.trans h
    obtain ⟨k, hk⟩ := hm
    omega

theorem erdos_828.variants.phi_dvd_self_iff_pow2_pow3 {n : ℕ} :
    φ n ∣ n ↔ n ≤ 1 ∨ ∃ᵉ (a > 0) (b), n = 2 ^ a * 3 ^ b := by
  constructor
  · intro h
    by_cases hn1 : n ≤ 1
    · exact Or.inl hn1
    right
    have hn0 : n ≠ 0 := by omega
    obtain ⟨a, m, hmodd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        simp only [pow_zero, one_mul] at hnm
        subst hnm
        have h2 : 2 < n := by
          obtain ⟨k, hk⟩ := hmodd
          omega
        obtain ⟨u, hu⟩ := Nat.totient_even h2
        have : 2 ∣ n := Nat.dvd_trans ⟨u, by omega⟩ h
        obtain ⟨k, hk⟩ := hmodd
        omega
      · exact ha
    have hcop : Nat.Coprime (2 ^ a) m :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hmodd))
    have htot : φ n = 2 ^ (a - 1) * φ m := by
      rw [hnm, Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two ha]
      simp
    have hpe : 2 ^ a = 2 ^ (a - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [htot, hnm, hpe, mul_assoc] at h
    have hm : φ m ∣ 2 * m := (Nat.mul_dvd_mul_iff_left (pow_pos two_pos _)).mp h
    obtain ⟨b, hb⟩ := odd_totient_dvd_two_mul_pow_three hmodd hm
    exact ⟨a, ha, b, by rw [hnm, hb]⟩
  · rintro (h | ⟨a, ha, b, rfl⟩)
    · interval_cases n <;> simp
    · have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two ha]
      obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        exact ⟨2, by simp [pow_succ]⟩
      · rw [Nat.totient_prime_pow Nat.prime_three hb]
        obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        exact ⟨3, by simp only [Nat.add_sub_cancel]; ring⟩

end OpenProofs.Erdos828
