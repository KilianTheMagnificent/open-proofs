import FormalConjectures.Wikipedia.WallSunSun

/-!
# `QuadraticAlgebra.discr_rat_of_modEq_one`

Upstream: `QuadraticAlgebra.discr_rat_of_modEq_one` (category textbook), `FormalConjectures/Wikipedia/WallSunSun.lean` line 39.
Proof idea: with `θ = (1 + ω) / 2` and `d = 1 - 4k`, `θ` is a root of `X² - X + k`, so the
`ℚ`-basis `1, θ` of `K = ℚ(√d)` lies in `𝓞 K`. Conversely, if `z = x + yω` is integral then
`z + z̄ = 2x` and `z z̄ = x² - d y²` are integers, so `d (2y)²` is an integer; `d` squarefree
forces `2y ∈ ℤ`, and `d ≡ 1 [ZMOD 4]` forces `2x ≡ 2y (mod 2)`, so the coordinates `x - y`, `2y`
of `z` in `1, θ` are integers. Hence the change-of-basis matrices between `1, θ` and the
integral basis are integral both ways, the discriminants agree
(`Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral`), and the trace matrix of `1, θ` is
`!![2, 1; 1, (1 + d) / 2]`, whose determinant is `d`.
-/

open Algebra (IsQuadraticExtension)
open NumberField
open QuadraticAlgebra

namespace OpenProofs.QuadraticAlgebra

/-- Coordinates with respect to `1, (1 + ω) / 2`. -/
noncomputable def wssCoordEquiv (a : ℚ) : QuadraticAlgebra ℚ a 0 ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun z := ![z.re - z.im, 2 * z.im]
  invFun v := ⟨v 0 + v 1 / 2, v 1 / 2⟩
  map_add' z w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r z := by ext i; fin_cases i <;> simp <;> ring
  left_inv z := by ext <;> simp
  right_inv v := by ext i; fin_cases i <;> simp; ring

/-- The `ℚ`-basis `1, (1 + ω) / 2`. -/
noncomputable def wssBasis (a : ℚ) : Module.Basis (Fin 2) ℚ (QuadraticAlgebra ℚ a 0) :=
  .ofEquivFun (wssCoordEquiv a)

theorem wssBasis_repr (a : ℚ) (z : QuadraticAlgebra ℚ a 0) :
    (wssBasis a).repr z = ![z.re - z.im, 2 * z.im] := rfl

theorem wssBasis_zero (a : ℚ) : wssBasis a 0 = 1 := by
  ext <;> simp [wssBasis, wssCoordEquiv]

theorem wssBasis_one (a : ℚ) : wssBasis a 1 = ⟨1 / 2, 1 / 2⟩ := by
  ext <;> simp [wssBasis, wssCoordEquiv]

theorem wss_trace_eq (a : ℚ) (z : QuadraticAlgebra ℚ a 0) :
    Algebra.trace ℚ (QuadraticAlgebra ℚ a 0) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis _ _), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  simp [QuadraticAlgebra.basis]
  ring

theorem wss_isIntegral_congr {A : Type*} [Ring A] (i₁ i₂ : Algebra ℤ A) {x : A}
    (h : @IsIntegral ℤ A _ _ i₁ x) : @IsIntegral ℤ A _ _ i₂ x := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

variable {d : ℤ} [Fact <| Squarefree d] [Fact <| d ≠ 1]

omit [Fact <| Squarefree d] [Fact <| d ≠ 1] in
/-- A rational `s` with `d * s ^ 2` integral, `d` squarefree, is an integer. -/
theorem wss_int_of_sq_mul (hd : Squarefree d) {s : ℚ} {m : ℤ} (hs : (d : ℚ) * s ^ 2 = m) :
    ∃ u : ℤ, (u : ℚ) = s := by
  refine ⟨s.num, ?_⟩
  have hden : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
  have key : d * s.num ^ 2 = m * (s.den : ℤ) ^ 2 := by
    have h1 : (s.num : ℚ) = s * s.den := by rw [Rat.mul_den_eq_num]
    have : (d : ℚ) * (s.num : ℚ) ^ 2 = m * (s.den : ℚ) ^ 2 := by
      rw [h1, ← hs]; ring
    exact_mod_cast this
  have hdvd : (s.den : ℤ) ^ 2 ∣ d * s.num ^ 2 := ⟨m, by rw [key]; ring⟩
  have hcop : IsCoprime ((s.den : ℤ) ^ 2) (s.num ^ 2) :=
    (Rat.isCoprime_num_den s).symm.pow
  have h2 : (s.den : ℤ) * s.den ∣ d := by
    have := hcop.dvd_of_dvd_mul_right hdvd
    simpa [sq] using this
  have hu : IsUnit (s.den : ℤ) := hd _ h2
  have : s.den = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> omega
  exact Rat.coe_int_num_of_den_eq_one this

theorem wss_coords_of_isIntegral (hd₄ : d ≡ 1 [ZMOD 4]) {z : QuadraticAlgebra ℚ (d : ℚ) 0}
    (hz : IsIntegral ℤ z) :
    (∃ m : ℤ, (m : ℚ) = z.re - z.im) ∧ ∃ m : ℤ, (m : ℚ) = 2 * z.im := by
  have hs : IsIntegral ℤ (star z) := by
    exact hz.map (starRingEnd (QuadraticAlgebra ℚ (d : ℚ) 0)).toIntAlgHom
  have htr : IsIntegral ℤ (QuadraticAlgebra.trace z) := by
    have := hz.add hs
    rw [← algebraMap_trace_eq_add_star] at this
    exact (isIntegral_algebraMap_iff algebraMap_injective).1 this
  have hnm : IsIntegral ℤ (QuadraticAlgebra.norm z) := by
    have := hz.mul hs
    rw [← algebraMap_norm_eq_mul_star] at this
    exact (isIntegral_algebraMap_iff algebraMap_injective).1 this
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 htr
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hnm
  rw [trace_def] at ht
  rw [norm_def] at hn
  simp only [eq_intCast] at ht hn
  obtain ⟨u, hu⟩ := wss_int_of_sq_mul (d := d) (Fact.out) (s := 2 * z.im) (m := t ^ 2 - 4 * n)
    (by push_cast; rw [ht, hn]; ring)
  obtain ⟨k, hk⟩ := hd₄.dvd
  have hint : (t - u) * (t + u) = 4 * (n - k * u ^ 2) := by
    have : ((t - u) * (t + u) : ℚ) = 4 * (n - k * u ^ 2) := by
      have hk' : (d : ℚ) = 1 - 4 * k := by
        have : ((1 - d : ℤ) : ℚ) = ((4 * k : ℤ) : ℚ) := by rw [hk]
        push_cast at this; linarith
      rw [hu, ht, hn]; linear_combination (4 * z.im ^ 2) * hk'
    exact_mod_cast this
  have h2 : 2 ∣ t - u := by
    by_contra hne
    have ho : Odd (t - u) := Int.not_even_iff_odd.1 (fun h => hne (even_iff_two_dvd.1 h))
    have ho' : Odd (t + u) := by
      have : t + u = (t - u) + 2 * u := by ring
      rw [this]; exact ho.add_even (even_two_mul u)
    have := Int.odd_mul.2 ⟨ho, ho'⟩
    rw [hint] at this
    exact (Int.not_even_iff_odd.2 this) ⟨2 * (n - k * u ^ 2), by ring⟩
  obtain ⟨w, hw⟩ := h2
  refine ⟨⟨w, ?_⟩, ⟨u, hu⟩⟩
  have : ((t - u : ℤ) : ℚ) = ((2 * w : ℤ) : ℚ) := by rw [hw]
  push_cast at this
  linarith

theorem discr_rat_of_modEq_one (hd₄ : d ≡ 1 [ZMOD 4]) : discr (QuadraticAlgebra ℚ d 0) = d := by
  classical
  obtain ⟨k, hk⟩ := hd₄.dvd
  have hk' : (d : ℚ) = 1 - 4 * k := by
    have : ((1 - d : ℤ) : ℚ) = ((4 * k : ℤ) : ℚ) := by rw [hk]
    push_cast at this; linarith
  have hθ : IsIntegral ℤ (wssBasis (d : ℚ) 1) := by
    rw [wssBasis_one]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C k, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    ext <;> simp [sq] <;> linarith
  have hc : ∀ j, IsIntegral ℤ (wssBasis (d : ℚ) j) := by
    intro j
    fin_cases j
    · simpa [wssBasis_zero] using isIntegral_one
    · exact hθ
  have h1 : ∀ i j, IsIntegral ℤ
      ((integralBasis (QuadraticAlgebra ℚ (d : ℚ) 0)).toMatrix (wssBasis (d : ℚ)) i j) := by
    intro i j
    rw [Module.Basis.toMatrix_apply]
    obtain ⟨y, hy⟩ : ∃ y : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0),
        algebraMap (𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) _ y = wssBasis (d : ℚ) j :=
      ⟨⟨_, (mem_integralClosure_iff ℤ _).2 (wss_isIntegral_congr _ _ (hc j))⟩, rfl⟩
    rw [← hy, integralBasis_repr_apply]
    exact isIntegral_algebraMap
  have h2 : ∀ i j, IsIntegral ℤ
      ((wssBasis (d : ℚ)).toMatrix (integralBasis (QuadraticAlgebra ℚ (d : ℚ) 0)) i j) := by
    intro i j
    rw [Module.Basis.toMatrix_apply, wssBasis_repr]
    have hz : IsIntegral ℤ (integralBasis (QuadraticAlgebra ℚ (d : ℚ) 0) j) := by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    obtain ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩⟩ := wss_coords_of_isIntegral hd₄ (wss_isIntegral_congr _ _ hz)
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [← hm1]; exact isIntegral_intCast m1
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← hm2]; exact isIntegral_intCast m2
  have hdisc : Algebra.discr ℚ (wssBasis (d : ℚ)) = d := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, wssBasis_zero, wssBasis_one]
    repeat erw [wss_trace_eq]
    simp
    ring
  rw [← Int.cast_inj (α := ℚ), coe_discr,
    Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral _ h1 h2, hdisc]

end OpenProofs.QuadraticAlgebra
