import FormalConjectures.GreensOpenProblems.«35»

/-!
# `Green35.variants.c_inf_lower_young`

Upstream: `Green35.variants.c_inf_lower_young` (category textbook), `FormalConjectures/GreensOpenProblems/35.lean` line 119.
Proof idea: for a unit-interval density `f`, `g = f ⋆ f` is nonnegative, integrable and has
integral `(∫ f)^2 = 1`. Hence `‖g‖₂² = ∫ g² ≤ ‖g‖_∞ ∫ g = ‖g‖_∞`. Taking infima,
`c 2 ^ 2 ≤ ‖f ⋆ f‖₂² ≤ ‖f ⋆ f‖_∞` for every density `f`, so `c 2 ^ 2 ≤ c ∞`.
-/

open MeasureTheory
open scoped Convolution ENNReal
open Green35 Green35.variants

namespace OpenProofs.Green35.variants

lemma green35_eLpNorm_two_sq_le_top (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g)
    (h1 : ∫ x, g x = 1) : eLpNorm g 2 ^ 2 ≤ eLpNorm g ∞ := by
  rw [eLpNorm_exponent_top]
  set M := eLpNormEssSup g volume
  have hsq : eLpNorm g 2 ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g) (p := 2) two_ne_zero
    simpa [ENNReal.rpow_two] using this
  have hone : ∫⁻ x, ‖g x‖ₑ = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)
    rw [h1, ENNReal.ofReal_one] at h
    rw [h]
    refine lintegral_congr fun x => ?_
    exact Real.enorm_of_nonneg (hg0 x)
  rw [hsq]
  calc ∫⁻ x, ‖g x‖ₑ ^ 2 ≤ ∫⁻ x, M * ‖g x‖ₑ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_le_eLpNormEssSup (μ := volume) (f := g)] with x hx
        rw [sq]
        gcongr
    _ = M * ∫⁻ x, ‖g x‖ₑ := lintegral_const_mul'' _ hgi.1.enorm
    _ = M := by rw [hone, mul_one]

lemma green35_conv_nonneg (f : ℝ → ℝ) (hf0 : ∀ x, 0 ≤ f x) : ∀ x, 0 ≤ (f ⋆ f) x := by
  intro x
  rw [convolution_def]
  exact integral_nonneg fun t => by simpa using mul_nonneg (hf0 t) (hf0 (x - t))

lemma green35_conv_integral (f : ℝ → ℝ) (hfi : Integrable f) (hf1 : ∫ x, f x = 1) :
    ∫ x, (f ⋆ f) x = 1 := by
  rw [integral_convolution _ hfi hfi, hf1]
  simp

lemma green35_density_bound (f : ℝ → ℝ) (hf : IsUnitIntervalDensity f) :
    eLpNorm (f ⋆ f) 2 ^ 2 ≤ eLpNorm (f ⋆ f) ∞ := by
  obtain ⟨hfi, hf0, -, hf1⟩ := hf
  exact green35_eLpNorm_two_sq_le_top _ (green35_conv_nonneg f hf0)
    (hfi.integrable_convolution _ hfi) (green35_conv_integral f hfi hf1)

theorem c_inf_lower_young : (c 2) ^ 2 ≤ c ∞ := by
  have hc : ∀ f, IsUnitIntervalDensity f → c 2 ≤ eLpNorm (f ⋆ f) 2 :=
    fun f hf => sInf_le ⟨f, hf, rfl⟩
  refine le_sInf ?_
  rintro r ⟨f, hf, rfl⟩
  have h2 : c 2 ^ 2 ≤ eLpNorm (f ⋆ f) 2 ^ 2 := by gcongr; exact hc f hf
  exact h2.trans (green35_density_bound f hf)

end OpenProofs.Green35.variants
