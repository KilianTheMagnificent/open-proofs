import FormalConjectures.ErdosProblems.«649»

/-!
# `Erdos649.erdos_649.variants.sampaio`

Upstream: `Erdos649.erdos_649.variants.sampaio` (category textbook), `FormalConjectures/ErdosProblems/649.lean` line 114.
Proof idea: if `(n + 1).maxPrimeFac = 2` then `n + 1 = 2 ^ k`. Since `19 ∣ n` we get
`2 ^ k ≡ 1 (mod 19)`; the order of `2` modulo `19` is `18`, so checking `k % 18` shows
`18 ∣ k`. Then `2 ^ 18 - 1 ∣ 2 ^ k - 1 = n`, and `73 ∣ 2 ^ 18 - 1`, so `73 ≤ n.maxPrimeFac = 19`,
a contradiction.
-/

open Erdos649

namespace OpenProofs.Erdos649

theorem erdos_649.variants.sampaio :
    ¬ ∃ n : ℕ, n.maxPrimeFac = 19 ∧ (n + 1).maxPrimeFac = 2 := by
  rintro ⟨n, hn, hn'⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp [Nat.maxPrimeFac_zero] at hn
  -- `n + 1` is a power of `2`.
  obtain ⟨k, hpow⟩ : ∃ k, n + 1 = 2 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
      (fun {q} hq hqd ↦
        le_antisymm (hn' ▸ Nat.le_maxPrimeFac (by omega) hq hqd) hq.two_le)⟩
  have h19 : 19 ∣ n := hn ▸ Nat.maxPrimeFac_dvd
  -- `2 ^ k ≡ 1 (mod 19)` forces `18 ∣ k`.
  have hmod : 2 ^ k % 19 = 2 ^ (k % 18) % 19 := by
    conv_lhs => rw [← Nat.div_add_mod k 18, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hk18 : k % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have hk : k % 18 = 0 := by
    interval_cases h : k % 18 <;> omega
  obtain ⟨j, rfl⟩ : 18 ∣ k := Nat.dvd_of_mod_eq_zero hk
  -- Hence `2 ^ 18 - 1 ∣ n`, and `73 ∣ 2 ^ 18 - 1`.
  have hdvd : 2 ^ 18 - 1 ∣ n := by
    have := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (Dvd.intro j rfl : 18 ∣ 18 * j)
    rwa [← hpow, Nat.add_sub_cancel] at this
  have h73 : 73 ∣ n := dvd_trans (by norm_num) hdvd
  have := Nat.le_maxPrimeFac hn0 (by norm_num) h73
  omega

end OpenProofs.Erdos649
