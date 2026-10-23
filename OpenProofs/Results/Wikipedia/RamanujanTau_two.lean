import FormalConjectures.Wikipedia.RamanujanTau

/-!
# Ramanujan τ: `τ_two`

Upstream: `RamanujanTau.τ_two` (category test): `τ 2 = -24`.

`τ 2` is the coefficient of `X ^ 2` in `Δ = X * ∏' n : ℕ+, (1 - X ^ n) ^ 24`, i.e. the coefficient
of `X` in the infinite product. The factors are multipliable in the product topology on `ℤ⟦X⟧`
(from Mathlib's `multipliable_one_sub_X_pow`, reindexed along `ℕ+ ≃ ℕ` and raised to the 24th
power); this is proved here, not taken from upstream. For a finite set `s ∋ 1` of indices, every
factor with `n ≥ 2` is `≡ 1 (mod X ^ 2)`, so the finite product is `(1 - X) ^ 24 * (1 + X ^ 2 * q)`,
whose coefficient of `X` is `-24`. Since `coeff 1` is continuous and `ℤ` is Hausdorff, the
coefficient of `X` in the infinite product, the limit of these eventually constant values, is
`-24`.

The multipliability lemma is also stated under the upstream name `multipliable`, whose upstream
proof is a placeholder (upstream `τ_one` depends on it).
-/

open RamanujanTau PowerSeries PowerSeries.WithPiTopology

namespace OpenProofs.RamanujanTau

/-- The factors of `Δ / X` form a multipliable family (product topology on `ℤ⟦X⟧`). -/
theorem multipliable_factors_tau2 :
    Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) := by
  have h : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) : PowerSeries ℤ) := by
    rw [← (Equiv.pnatEquivNat.symm).multipliable_iff]
    convert multipliable_one_sub_X_pow ℤ using 2 with n
    simp
  exact h.pow 24

/-- `X ^ 2 ∣ f - 1` is preserved by finite products. -/
theorem dvd_prod_sub_one_tau2 {ι : Type*} (s : Finset ι) (g : ι → PowerSeries ℤ)
    (hg : ∀ i ∈ s, (X : PowerSeries ℤ) ^ 2 ∣ g i - 1) :
    (X : PowerSeries ℤ) ^ 2 ∣ (∏ i ∈ s, g i) - 1 := by
  refine Finset.prod_induction g (fun f => (X : PowerSeries ℤ) ^ 2 ∣ f - 1) ?_ (by simp) hg
  intro a b ha hb
  have : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [this]
  exact (Dvd.dvd.mul_right ha b).add hb

theorem coeff_one_one_sub_X_pow_tau2 (n : ℕ) :
    coeff 1 ((1 - X : PowerSeries ℤ) ^ n) = -n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_sub, mul_one, map_sub, ih, coeff_succ_mul_X]
    simp [coeff_zero_eq_constantCoeff]
    ring

theorem coeff_one_finset_prod_tau2 (s : Finset ℕ+) (hs : 1 ∈ s) :
    coeff 1 (∏ i ∈ s, ((1 - X ^ (i : ℕ)) ^ 24 : PowerSeries ℤ)) = -24 := by
  rw [← Finset.mul_prod_erase s _ hs]
  obtain ⟨q, hq⟩ : (X : PowerSeries ℤ) ^ 2 ∣
      (∏ i ∈ s.erase 1, ((1 - X ^ (i : ℕ)) ^ 24 : PowerSeries ℤ)) - 1 := by
    apply dvd_prod_sub_one_tau2
    intro i hi
    have hi2 : 2 ≤ (i : ℕ) := by
      have := (Finset.mem_erase.1 hi).1
      have h1 := i.pos
      have : (i : ℕ) ≠ 1 := fun h => this (PNat.coe_eq_one_iff.1 h)
      omega
    have h1 : (X : PowerSeries ℤ) ^ 2 ∣ (1 - X ^ (i : ℕ)) - 1 := by
      rw [sub_sub_cancel_left]
      exact (dvd_neg).2 (pow_dvd_pow X hi2)
    have h2 := sub_dvd_pow_sub_pow (1 - X ^ (i : ℕ) : PowerSeries ℤ) 1 24
    rw [one_pow] at h2
    exact h1.trans h2
  rw [sub_eq_iff_eq_add] at hq
  rw [hq]
  simp only [PNat.one_coe, pow_one]
  rw [mul_add, mul_one, map_add, coeff_one_one_sub_X_pow_tau2, mul_left_comm,
    coeff_X_pow_mul']
  simp

theorem τ_two : τ 2 = -24 := by
  have hP := (multipliable_factors_tau2).hasProd
  have h1 := ((continuous_coeff (R := ℤ) 1).tendsto _).comp hP
  have h2 : Filter.Tendsto
      (fun s : Finset ℕ+ ↦ coeff 1 (∏ i ∈ s, ((1 - X ^ (i : ℕ)) ^ 24 : PowerSeries ℤ)))
      Filter.atTop (nhds (-24)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {1}] with s hs
    exact (coeff_one_finset_prod_tau2 s (hs (Finset.mem_singleton_self 1))).symm
  have h3 := tendsto_nhds_unique h1 h2
  show coeff 2 (X * ∏' (n : ℕ+), (1 - X ^ (n : ℕ)) ^ 24) = -24
  rw [coeff_succ_X_mul]
  exact h3

/-- Upstream `RamanujanTau.multipliable` (category API), restated verbatim: the helper above. -/
theorem multipliable : Multipliable fun n : ℕ+ ↦ ((1 - X ^ (n : ℕ)) ^ 24 : PowerSeries ℤ) :=
  multipliable_factors_tau2

end OpenProofs.RamanujanTau
