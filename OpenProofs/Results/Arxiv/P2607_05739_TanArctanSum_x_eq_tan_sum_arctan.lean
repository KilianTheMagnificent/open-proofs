import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-!
# `Arxiv.«2607.05739».x_eq_tan_sum_arctan`

Upstream: `Arxiv.«2607.05739».x_eq_tan_sum_arctan` (category textbook), `FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean` line 80.
Proof idea: by induction on `n`, `A n = r * cos θ` and `B n = r * sin θ` for some `r > 0`, where
`θ = ∑ arctan k`: multiplying by `1 + i(n+1)` multiplies the modulus by `√(1 + (n+1)²)` and adds
`arctan (n+1)` to the angle (`Real.cos_arctan`, `Real.sin_arctan`, angle addition). Then
`B n / A n = (r sin θ) / (r cos θ) = sin θ / cos θ = tan θ`, also when `cos θ = 0`.
-/

open Finset
open Arxiv.«2607.05739»

namespace OpenProofs.Arxiv.«2607.05739»

theorem tanArctanSum_polar_aux (n : ℕ) : ∃ r : ℝ, 0 < r ∧
    ((A n : ℤ) : ℝ) = r * Real.cos (∑ k ∈ Finset.Icc 1 n, Real.arctan k) ∧
    ((B n : ℤ) : ℝ) = r * Real.sin (∑ k ∈ Finset.Icc 1 n, Real.arctan k) := by
  induction n with
  | zero => exact ⟨1, one_pos, by simp [A, gaussProd], by simp [B, gaussProd]⟩
  | succ n ih =>
    obtain ⟨r, hr, hA, hB⟩ := ih
    have hAs : A (n+1) = A n - B n * ((n:ℤ)+1) := by
      simp [A, B, gaussProd, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]; ring
    have hBs : B (n+1) = A n * ((n:ℤ)+1) + B n := by
      simp [A, B, gaussProd, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    set θ := ∑ k ∈ Finset.Icc 1 n, Real.arctan (k : ℝ) with hθ
    have hsum : ∑ k ∈ Finset.Icc 1 (n+1), Real.arctan (k : ℝ) = θ + Real.arctan ((n:ℝ)+1) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]; push_cast; rfl
    have hs : 0 < Real.sqrt (1 + ((n:ℝ)+1)^2) := Real.sqrt_pos.mpr (by positivity)
    refine ⟨r * Real.sqrt (1 + ((n:ℝ)+1)^2), mul_pos hr hs, ?_, ?_⟩
    · rw [hsum, Real.cos_add, Real.cos_arctan, Real.sin_arctan, hAs]
      push_cast
      rw [hA, hB]
      field_simp
    · rw [hsum, Real.sin_add, Real.cos_arctan, Real.sin_arctan, hBs]
      push_cast
      rw [hA, hB]
      field_simp
      ring

theorem x_eq_tan_sum_arctan (n : ℕ) (hn : 1 ≤ n) :
    (x n : ℝ) = Real.tan (∑ k ∈ Finset.Icc 1 n, Real.arctan k) := by
  obtain ⟨r, hr, hA, hB⟩ := tanArctanSum_polar_aux n
  rw [x]
  push_cast
  rw [hA, hB, Real.tan_eq_sin_div_cos, mul_div_mul_left _ _ hr.ne']

end OpenProofs.Arxiv.«2607.05739»
