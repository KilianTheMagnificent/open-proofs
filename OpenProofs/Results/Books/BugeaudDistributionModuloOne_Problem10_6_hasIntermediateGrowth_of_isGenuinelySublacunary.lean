import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6

/-!
# `Bugeaud06.hasIntermediateGrowth_of_isGenuinelySublacunary`

Upstream: `Bugeaud06.hasIntermediateGrowth_of_isGenuinelySublacunary` (category API), `FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean` line 199.
Proof idea: past an index `N ≥ 2` where the ratio floor holds, every `m k` is positive (a zero
term would make the ratio `0 < 1 + c / log k`). For a fixed `n ≥ N`, every `k < n` has
`log k ≤ log n`, so iterating the floor gives `m n ≥ (1 + c / log n) ^ (n - N) * m N ≥
(1 + c / log n) ^ (n - N)`. With `log (1 + y) ≥ 1 - 1 / (1 + y)` this is at least
`exp ((n - N) * c / (log n + c))`. Eventually `log n ≥ c`, `n ≥ 2 N` and
`log n ≤ (c / 4) n ^ (1 - α)` (`isLittleO_log_rpow_atTop`), and together these give
`n ^ α ≤ (n - N) * c / (log n + c)`.
-/

open Filter
open Bugeaud06

namespace OpenProofs.Bugeaud06

theorem hasIntermediateGrowth_of_isGenuinelySublacunary {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    HasIntermediateGrowth α m := by
  obtain ⟨c, hc, hev⟩ := h
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set N := max N0 2 with hN
  have hN2 : 2 ≤ N := le_max_right N0 2
  have hNN0 : N0 ≤ N := le_max_left N0 2
  have hlogpos : ∀ k : ℕ, N ≤ k → 0 < Real.log k := fun k hk => by
    apply Real.log_pos
    have : (2 : ℝ) ≤ k := by exact_mod_cast hN2.trans hk
    linarith
  have hpos : ∀ k : ℕ, N ≤ k → 0 < m k := fun k hk => by
    rcases Nat.eq_zero_or_pos (m k) with h0 | h0
    · exfalso
      have h1 := hN0 k (hNN0.trans hk)
      rw [h0] at h1
      have h2 : 0 < c / Real.log k := div_pos hc (hlogpos k hk)
      simp at h1
      linarith
    · exact h0
  have hstep : ∀ k : ℕ, N ≤ k → (1 + c / Real.log k) * m k ≤ m (k + 1) := fun k hk => by
    have h1 := hN0 k (hNN0.trans hk)
    have hmk : (0 : ℝ) < m k := by exact_mod_cast hpos k hk
    rwa [le_div_iff₀ hmk] at h1
  have hiter : ∀ n j : ℕ, N + j ≤ n → (1 + c / Real.log n) ^ j * m N ≤ m (N + j) := by
    intro n j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hk : N ≤ N + j := by omega
      have hL := hlogpos (N + j) hk
      have hxpos : (0 : ℝ) < ((N + j : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ ((N + j : ℕ) : ℝ) := by exact_mod_cast hN2.trans hk
        linarith
      have hle : Real.log ((N + j : ℕ) : ℝ) ≤ Real.log n :=
        Real.log_le_log hxpos (by exact_mod_cast (by omega : N + j ≤ n))
      have hy : c / Real.log n ≤ c / Real.log ((N + j : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hc.le hL hle
      have h1 : 0 ≤ 1 + c / Real.log n := by
        have := hlogpos n (by omega)
        positivity
      calc (1 + c / Real.log n) ^ (j + 1) * m N
          = (1 + c / Real.log n) * ((1 + c / Real.log n) ^ j * m N) := by ring
        _ ≤ (1 + c / Real.log n) * m (N + j) := mul_le_mul_of_nonneg_left ih' h1
        _ ≤ (1 + c / Real.log ((N + j : ℕ) : ℝ)) * m (N + j) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ ≤ m (N + j + 1) := hstep (N + j) hk
  have hr : 0 < 1 - α := by linarith
  have hlo := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop hr).def (by positivity : 0 < c / 4))
  have hlogc := tendsto_natCast_atTop_atTop.eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop c)
  filter_upwards [hlo, hlogc, eventually_ge_atTop (2 * N)] with n hn1 hn2 hn3
  have hnN : N ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
    linarith
  set L := Real.log n with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le hc hn2
  set P := (n : ℝ) ^ α with hPdef
  set Q := (n : ℝ) ^ (1 - α) with hQdef
  have hP : 0 < P := Real.rpow_pos_of_pos hnpos _
  have hQ : 0 < Q := Real.rpow_pos_of_pos hnpos _
  have hPQ : P * Q = n := by
    rw [hPdef, hQdef, ← Real.rpow_add hnpos]
    norm_num
  have hLQ : L ≤ c / 4 * Q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLpos, abs_of_pos hQ] at hn1
    exact hn1
  have hmain : P ≤ ((n - N : ℕ) : ℝ) * Real.log (1 + c / L) := by
    have hcast : ((n - N : ℕ) : ℝ) = (n : ℝ) - N := by
      rw [Nat.cast_sub hnN]
    have hlog : c / (L + c) ≤ Real.log (1 + c / L) := by
      have h1 : (0 : ℝ) < 1 + c / L := by positivity
      have h2 := Real.one_sub_inv_le_log_of_pos h1
      have h3 : 1 - (1 + c / L)⁻¹ = c / (L + c) := by
        field_simp
        ring
      linarith
    have hn3' : (2 * N : ℝ) ≤ n := by exact_mod_cast hn3
    have hnN' : (0 : ℝ) ≤ (n : ℝ) - N := by linarith
    calc P ≤ ((n : ℝ) - N) * (c / (L + c)) := by
          rw [mul_div_assoc', le_div_iff₀ (by linarith)]
          have e1 : c * (P * Q) = c * n := by rw [hPQ]
          nlinarith [mul_le_mul_of_nonneg_left hLQ hP.le, mul_le_mul_of_nonneg_left hn2 hP.le,
            mul_le_mul_of_nonneg_left hn3' hc.le]
      _ ≤ ((n : ℝ) - N) * Real.log (1 + c / L) := mul_le_mul_of_nonneg_left hlog hnN'
      _ = ((n - N : ℕ) : ℝ) * Real.log (1 + c / L) := by rw [hcast]
  have hy : (0 : ℝ) < 1 + c / L := by positivity
  have hgrow : Real.exp P ≤ (1 + c / L) ^ (n - N) := by
    calc Real.exp P ≤ Real.exp (((n - N : ℕ) : ℝ) * Real.log (1 + c / L)) :=
          Real.exp_le_exp.2 hmain
      _ = Real.exp (Real.log (1 + c / L)) ^ (n - N) := Real.exp_nat_mul _ _
      _ = (1 + c / L) ^ (n - N) := by rw [Real.exp_log hy]
  have hit := hiter n (n - N) (by omega)
  rw [show N + (n - N) = n by omega] at hit
  have hmN : (1 : ℝ) ≤ m N := by exact_mod_cast hpos N le_rfl
  have hpow : 0 ≤ (1 + c / L) ^ (n - N) := by positivity
  calc Real.exp P ≤ (1 + c / L) ^ (n - N) := hgrow
    _ ≤ (1 + c / L) ^ (n - N) * m N := le_mul_of_one_le_right hpow hmN
    _ ≤ m n := hit

end OpenProofs.Bugeaud06
