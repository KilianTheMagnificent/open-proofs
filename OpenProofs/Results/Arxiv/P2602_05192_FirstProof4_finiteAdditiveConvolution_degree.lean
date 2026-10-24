import FormalConjectures.Arxiv.«2602.05192».FirstProof4

/-!
# `Arxiv.«2602.05192».finiteAdditiveConvolution_degree`

Upstream: `Arxiv.«2602.05192».finiteAdditiveConvolution_degree` (category test), `FormalConjectures/Arxiv/2602.05192/FirstProof4.lean` line 65.
Proof idea: every summand `c k • X^(n - k)` has degree at most `n`, so the convolution has
degree at most `n`. Only `k = 0` contributes to the coefficient of `X^n`, and `c 0` reduces to
`(n! * n!) / (n! * n!) * p.coeff n * q.coeff n`, the product of the two (nonzero) leading
coefficients. Hence the coefficient of `X^n` is nonzero and the degree is exactly `n`.
-/

open Polynomial Finset ENNReal
open scoped Nat
open Arxiv.«2602.05192»

namespace OpenProofs.Arxiv.«2602.05192»

variable {F : Type} [Field F]

theorem finiteAdditiveConvolution_degree (n : ℕ) (p q : ℝ[X])
  (hp : p.degree = n) (hq : q.degree = n):
    (finiteAdditiveConvolution n p q).degree = n := by
  have hpn : p.natDegree = n := natDegree_eq_of_degree_eq_some hp
  have hqn : q.natDegree = n := natDegree_eq_of_degree_eq_some hq
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  have hpc : p.coeff n ≠ 0 := by
    rw [← hpn]; exact leadingCoeff_ne_zero.mpr hp0
  have hqc : q.coeff n ≠ 0 := by
    rw [← hqn]; exact leadingCoeff_ne_zero.mpr hq0
  apply degree_eq_of_le_of_coeff_ne_zero
  · simp only [finiteAdditiveConvolution]
    refine (degree_sum_le _ _).trans ?_
    apply Finset.sup_le
    intro k _
    refine (degree_smul_le _ _).trans ?_
    refine (degree_X_pow_le (n - k)).trans ?_
    exact_mod_cast Nat.sub_le n k
  · simp only [finiteAdditiveConvolution]
    rw [Polynomial.finsetSum_coeff]
    conv_lhs =>
      arg 2; ext k
      rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow]
    simp only [smul_eq_mul]
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.sub_zero, ite_true, mul_one, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      have h_ne : (n ! : ℝ) ≠ 0 := by positivity
      have : ((n ! : ℝ) * n !) / (n ! * n !) = 1 := div_self (mul_ne_zero h_ne h_ne)
      rw [this, one_mul]
      exact mul_ne_zero hpc hqc
    · intro k hk hk0
      have := Finset.mem_range.mp hk
      have : n ≠ n - k := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end OpenProofs.Arxiv.«2602.05192»
