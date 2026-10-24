import FormalConjectures.ErdosProblems.«91»

/-!
# `Erdos91.erdos_91.test.dissimilar_circleSeven_wheelSeven`

Upstream: `Erdos91.erdos_91.test.dissimilar_circleSeven_wheelSeven` (category test), `FormalConjectures/ErdosProblems/91.lean` line 132.
Proof idea: a dilation scales every distance by the same nonzero ratio, so it preserves and
reflects the equality case `dist a c + dist c b = dist a b` of the triangle inequality. The wheel
contains three distinct points `(0, √3/2)`, `(1, √3/2)`, `(2, √3/2)` in that equality case; their
preimages in the heptagon would then be three distinct points with the middle one strictly
between the others (`dist_add_dist_eq_iff`). But every heptagon point is at the same distance
from the centre `(cx, cy)`, and a point strictly between two points of a sphere lies strictly
inside it (`Sbtw.dist_lt_max_dist`), a contradiction.
-/

open Finset EuclideanGeometry Filter
open Erdos91

namespace OpenProofs.Erdos91

theorem circleSeven_dist_centre_eq {p : ℝ²} (hp : p ∈ circleSeven) :
    dist p !₂[1 / (2 * Real.sin (Real.pi / 7)) * Real.cos (Real.pi / 7),
      1 / (2 * Real.sin (Real.pi / 7)) * Real.sin (4 * Real.pi / 7)] =
      √((1 / (2 * Real.sin (Real.pi / 7))) ^ 2) := by
  simp only [circleSeven, Finset.mem_image] at hp
  obtain ⟨k, -, rfl⟩ := hp
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  congr 1
  simp only [Real.dist_eq, sq_abs]
  simp
  have := Real.cos_sq_add_sin_sq (2 * Real.pi * ↑k / 7)
  linear_combination (1 / (2 * Real.sin (Real.pi / 7))) ^ 2 * this

theorem erdos_91.test.dissimilar_circleSeven_wheelSeven :
    ¬DilationEquivSimilar circleSeven wheelSeven := by
  rintro ⟨f, hf⟩
  have hP : !₂[(0 : ℝ), Real.sqrt 3 / 2] ∈ (f '' circleSeven) := by
    rw [hf]; simp [wheelSeven]
  have hQ : !₂[(1 : ℝ), Real.sqrt 3 / 2] ∈ (f '' circleSeven) := by
    rw [hf]; simp [wheelSeven]
  have hR : !₂[(2 : ℝ), Real.sqrt 3 / 2] ∈ (f '' circleSeven) := by
    rw [hf]; simp [wheelSeven]
  obtain ⟨a, ha, hfa⟩ := hP
  obtain ⟨c, hc, hfc⟩ := hQ
  obtain ⟨b, hb, hfb⟩ := hR
  have hd : ∀ x y : ℝ, dist (!₂[x, Real.sqrt 3 / 2]) (!₂[y, Real.sqrt 3 / 2]) = |x - y| := by
    intro x y
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
    simp [Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hsum : dist (f a) (f c) + dist (f c) (f b) = dist (f a) (f b) := by
    rw [hfa, hfc, hfb, hd, hd, hd]; norm_num
  have hr := Dilation.ratio_ne_zero f
  simp only [Dilation.dist_eq] at hsum
  have hsum' : dist a c + dist c b = dist a b := by
    have hr' : (Dilation.ratio f : ℝ) ≠ 0 := by exact_mod_cast hr
    apply mul_left_cancel₀ hr'
    linarith
  have hw : Wbtw ℝ a c b := dist_add_dist_eq_iff.mp hsum'
  have hca : c ≠ a := by
    rintro rfl
    rw [hfa] at hfc
    have := congrArg (fun p : ℝ² => p 0) hfc
    simp at this
  have hcb : c ≠ b := by
    rintro rfl
    rw [hfc] at hfb
    have := congrArg (fun p : ℝ² => p 0) hfb
    norm_num at this
  have hs : Sbtw ℝ a c b := ⟨hw, hca, hcb⟩
  have hlt := hs.dist_lt_max_dist !₂[1 / (2 * Real.sin (Real.pi / 7)) * Real.cos (Real.pi / 7),
      1 / (2 * Real.sin (Real.pi / 7)) * Real.sin (4 * Real.pi / 7)]
  rw [circleSeven_dist_centre_eq ha, circleSeven_dist_centre_eq hb,
    circleSeven_dist_centre_eq hc, max_self] at hlt
  exact lt_irrefl _ hlt

end OpenProofs.Erdos91
