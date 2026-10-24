import FormalConjectures.OptimizationConstants.«7a»

/-!
# `Constant7a.two_le_irrationalityExponent`

Upstream: `Constant7a.two_le_irrationalityExponent` (category textbook), `FormalConjectures/OptimizationConstants/7a.lean` line 98.
Proof idea: by `le_irrationalityExponent_iff` it suffices to show `LiouvilleWith z x` for every
`z < 2`, and by monotonicity it suffices to show `LiouvilleWith 2 x`. Mathlib's Dirichlet
theorem gives infinitely many rationals `q` with `|x - q| < 1 / q.den ^ 2`. Their denominators
are unbounded: with bounded denominators the numerators are bounded too (since `|x - q| < 1`),
so there would be only finitely many such `q`. Hence the set of `n` admitting `m` with
`|x - m / n| < 1 / n ^ 2` (and `x ≠ m / n` by irrationality) is infinite, which is
`LiouvilleWith 2 x` with constant `1`.
-/

open Real ENNReal Set NNReal
open Constant7a

namespace OpenProofs.Constant7a

theorem two_le_irrationalityExponent {x : ℝ} (hx : Irrational x) :
    2 ≤ irrationalityExponent x := by
  rw [le_irrationalityExponent_iff]
  intro z hz
  have h2 : LiouvilleWith 2 x := by
    set S := {q : ℚ | |x - q| < 1 / (q.den : ℝ) ^ 2} with hS
    have hSinf : S.Infinite := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
    have hden : (Rat.den '' S).Infinite := by
      intro hfin
      obtain ⟨N, hN⟩ := hfin.bddAbove
      apply hSinf
      let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
      have hinj : Function.Injective f := by
        intro a b hab
        simp only [f, Prod.mk_inj] at hab
        rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
      set B : ℤ := ⌈(|x| + 1) * N⌉ with hB
      have H : f '' S ⊆ Set.Icc (-B) B ×ˢ Set.Iic N := by
        rintro _ ⟨q, hq, rfl⟩
        have hqd : q.den ≤ N := hN ⟨q, hq, rfl⟩
        refine ⟨?_, hqd⟩
        have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
        have hN1 : (q.den : ℝ) ≤ N := by exact_mod_cast hqd
        have hlt : |x - q| < 1 := by
          refine lt_of_lt_of_le hq ?_
          rw [div_le_one (by positivity)]
          nlinarith
        have hq' : |(q : ℝ)| < |x| + 1 := by
          have := abs_sub_abs_le_abs_sub (q : ℝ) x
          rw [abs_sub_comm] at hlt
          linarith
        have hnum : |(q.num : ℝ)| ≤ (|x| + 1) * N := by
          have hc : (q.num : ℝ) = q * q.den := by
            rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_mul, Rat.mul_den_eq_num]
          rw [hc, abs_mul, Nat.abs_cast]
          calc |(q : ℝ)| * q.den ≤ (|x| + 1) * q.den := by gcongr
            _ ≤ (|x| + 1) * N := by gcongr
        have hB' : |q.num| ≤ B := by
          have : ((|q.num| : ℤ) : ℝ) ≤ (B : ℝ) := by
            rw [hB, Int.cast_abs]
            exact hnum.trans (Int.le_ceil _)
          exact_mod_cast this
        exact abs_le.mp hB'
      exact (((Set.finite_Icc _ _).prod (Set.finite_Iic N)).subset H).of_finite_image hinj.injOn
    refine ⟨1, ?_⟩
    rw [Nat.frequently_atTop_iff_infinite]
    refine hden.mono ?_
    rintro _ ⟨q, hq, rfl⟩
    have hc : ((q.num : ℝ) / q.den) = q := by exact_mod_cast Rat.num_div_den q
    refine ⟨q.num, ?_, ?_⟩
    · rw [hc]; exact hx.ne_rat q
    · rw [hc]
      have hq2 : |x - q| < 1 / (q.den : ℝ) ^ 2 := hq
      simpa [Real.rpow_two] using hq2
  have hz' : (z : ℝ) ≤ 2 := by
    have : z < 2 := by exact_mod_cast hz
    exact_mod_cast this.le
  exact h2.mono hz'

end OpenProofs.Constant7a
