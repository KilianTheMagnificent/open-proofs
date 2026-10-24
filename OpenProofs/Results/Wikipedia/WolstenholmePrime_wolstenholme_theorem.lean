import FormalConjectures.Wikipedia.WolstenholmePrime
import OpenProofs.Results.Wikipedia.WolstenholmePrime_wolstenholme_bernoulli

/-!
# `WolstenholmePrime.wolstenholme_theorem`

Upstream: `WolstenholmePrime.wolstenholme_theorem` (category textbook), `FormalConjectures/Wikipedia/WolstenholmePrime.lean` line 39.
Proof idea: for `p = 5, 7` compute directly. For `p > 7` reuse step A of the proof of
`wolstenholme_bernoulli`: with `f(x) = ∏_{k=1}^{p-1} (x + k)`, the symmetry `f(-p) = f(0)` gives
`(p-1)! (C(2p-1, p-1) - 1) ≡ 2 p² e_{p-3}(1, …, p-1) (mod p⁴)`. Since `p ∣ e_j(1, …, p-1)` for
`1 ≤ j ≤ p - 2` (Newton's identities), the right side is divisible by `p³`, and `(p-1)!` is
prime to `p`, so `p³ ∣ C(2p-1, p-1) - 1`.
-/

open WolstenholmePrime Finset

namespace OpenProofs.WolstenholmePrime

theorem wolstenholme_theorem (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by
  by_cases h7 : 7 < p
  · have := Fact.mk hp
    have hA := wbern_stepA p h7
    obtain ⟨c, hc⟩ := wbern_esymm_dvd p (p - 3) (by omega) (by omega)
    have hpF : IsCoprime ((p : ℤ) ^ 3) ((p - 1).factorial : ℤ) := by
      have : IsCoprime ((p ^ 3 : ℕ) : ℤ) ((p - 1).factorial : ℕ) := by
        rw [Nat.isCoprime_iff_coprime]
        exact Nat.Coprime.pow_left 3
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by rw [hp.dvd_factorial]; omega))
      exact_mod_cast this
    rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
    push_cast
    apply hpF.dvd_of_dvd_mul_left
    have h4 : (p : ℤ) ^ 3 ∣ (p : ℤ) ^ 4 := pow_dvd_pow _ (by norm_num)
    rw [hc] at hA
    have h2 : (p : ℤ) ^ 3 ∣ 2 * (p : ℤ) ^ 2 * ((p : ℤ) * c) := ⟨2 * c, by ring⟩
    have := dvd_add (h4.trans hA) h2
    simpa using this
  · interval_cases p <;> first | decide | norm_num at hp

end OpenProofs.WolstenholmePrime
