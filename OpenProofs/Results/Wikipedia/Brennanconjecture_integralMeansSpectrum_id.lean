import FormalConjectures.Wikipedia.Brennanconjecture

/-!
# `BrennanConjecture.integralMeansSpectrum_id`

Upstream: `BrennanConjecture.integralMeansSpectrum_id` (category test), `FormalConjectures/Wikipedia/Brennanconjecture.lean` line 72.
Proof idea: The identity has derivative one, so the integral in the numerator
is constant. As the radius tends to one from below, the absolute value of
the logarithm of one minus the radius tends to infinity. The quotient
therefore tends to zero, and its limit superior is zero.
-/

open Complex Filter MeasureTheory Set Topology
open BrennanConjecture

namespace OpenProofs.BrennanConjecture

theorem integralMeansSpectrum_id (τ : ℝ) : integralMeansSpectrum id τ = 0 := by
  have hsub : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun r : ℝ => 1 - r) := by fun_prop
      simpa only [sub_self] using
        hc.continuousWithinAt.tendsto (s := Iio (1 : ℝ)) (x := 1)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < 1 - r
      change r < 1 at hr
      exact sub_pos.mpr hr
  have hdenom : Tendsto (fun r : ℝ => |Real.log (1 - r)|) (𝓝[<] 1) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)
  simp only [integralMeansSpectrum, deriv_id, norm_one, Real.one_rpow]
  exact (tendsto_const_nhds.div_atTop hdenom).limsup_eq

end OpenProofs.BrennanConjecture
