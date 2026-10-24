import FormalConjectures.Wikipedia.Mahler32

/-!
# `Mahler32.mahler_conjecture.variants.consequence`

Upstream: `Mahler32.mahler_conjecture.variants.consequence` (category textbook), `FormalConjectures/Wikipedia/Mahler32.lean` line 48.
Proof idea: every sequence of fractional parts lies in `[0, 1)`, so for every `θ > 0` the
limsup minus the liminf is nonnegative and the set defining `Ω` is bounded below. If `x` is a
Z-number, take `θ = x`: the fractional parts `{x (3/2)^n}` are below `1/2` for `n ≥ 1`, so the
limsup is at most `1/2` and the liminf is at least `0`. Hence `Ω(3/2) ≤ 1/2`, contradicting `H`.
-/

open Mahler32

namespace OpenProofs.Mahler32

theorem mahler_frac_bddAbove (θ α : ℝ) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n : ℕ ↦ Int.fract (θ * α ^ n)) :=
  Filter.isBoundedUnder_of ⟨1, fun _ ↦ (Int.fract_lt_one _).le⟩

theorem mahler_frac_bddBelow (θ α : ℝ) :
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n : ℕ ↦ Int.fract (θ * α ^ n)) :=
  Filter.isBoundedUnder_of ⟨0, fun _ ↦ Int.fract_nonneg _⟩

theorem mahler_conjecture.variants.consequence (H : 1 / 2 < Ω (3 / 2)) :
    type_of% mahler_conjecture := by
  intro x hx
  obtain ⟨hx0, hfr⟩ := hx
  have hbdd : BddBelow {Filter.atTop.limsup (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n))
      - Filter.atTop.liminf (fun n ↦ Int.fract (θ * (3 / 2 : ℝ) ^ n)) |
      (θ : ℝ) (_ : 0 < θ)} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨θ, _, rfl⟩
    exact sub_nonneg.mpr
      (Filter.liminf_le_limsup (mahler_frac_bddAbove θ _) (mahler_frac_bddBelow θ _))
  have hmem : Filter.atTop.limsup (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n))
      - Filter.atTop.liminf (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ≤ 1 / 2 := by
    have h1 : Filter.atTop.limsup (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) ≤ 1 / 2 := by
      apply Filter.limsup_le_of_le (mahler_frac_bddBelow x _).isCoboundedUnder_le
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      exact (hfr n hn).le
    have h2 : 0 ≤ Filter.atTop.liminf (fun n ↦ Int.fract (x * (3 / 2 : ℝ) ^ n)) := by
      apply Filter.le_liminf_of_le (mahler_frac_bddAbove x _).isCoboundedUnder_ge
      exact Filter.Eventually.of_forall fun n ↦ Int.fract_nonneg _
    linarith
  have hle : Ω (3 / 2) ≤ 1 / 2 :=
    (csInf_le hbdd ⟨x, hx0, rfl⟩).trans hmem
  linarith

end OpenProofs.Mahler32
