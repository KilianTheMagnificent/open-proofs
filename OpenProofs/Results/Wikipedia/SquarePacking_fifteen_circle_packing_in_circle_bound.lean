import FormalConjectures.Wikipedia.SquarePacking

/-!
# `SquarePacking.fifteen_circle_packing_in_circle_bound`

Upstream: `SquarePacking.fifteen_circle_packing_in_circle_bound` (category textbook), `FormalConjectures/Wikipedia/SquarePacking.lean` line 211.

Proof idea: explicit packing by translations. Let `t = √(1 + 2/√5) = tan 54°`, a root of
`5 t⁴ - 10 t² + 1 = 0`. Five inner unit discs sit at the vertices of a regular pentagon of side 2
(rotations of `(1, t)` by multiples of 72°); ten outer discs sit at the rotations of `(±1, t + 2)`,
two above each pentagon edge. Since `√5 = 5 (t² - 1) / 2`, the cosines and sines of multiples of
72° are polynomials in `t`, so every centre has coordinates that are cubic polynomials in `t`.
The outer centres have squared norm exactly `t² + 4t + 5 = 6 + 2/√5 + 4t`, the square of the
container radius minus one; all pairwise squared distances are at least 4. Both facts are checked
by `linarith` after reducing powers `t⁴, t⁵, t⁶` with the quartic and bounding `t, t², t³`.
-/

open EuclideanGeometry
open scoped NNReal
open SquarePacking

namespace OpenProofs.SquarePacking

/-- `tan 54° = √(1 + 2/√5)`. -/
noncomputable def sq15T : ℝ := Real.sqrt (1 + 2 / Real.sqrt 5)

lemma sq15T_sq : sq15T ^ 2 = 1 + 2 / Real.sqrt 5 := by
  unfold sq15T
  rw [Real.sq_sqrt]
  positivity

lemma sq15T_pos : 0 < sq15T := by
  unfold sq15T
  positivity

lemma sq15T_quartic : sq15T ^ 4 = 2 * sq15T ^ 2 - 1 / 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := by positivity
  have h' : (sq15T ^ 2 - 1) * Real.sqrt 5 = 2 := by
    rw [sq15T_sq]
    field_simp
    ring
  linear_combination (-(sq15T ^ 2 - 1) ^ 2 / 5) * h5 +
    (((sq15T ^ 2 - 1) * Real.sqrt 5 + 2) / 5) * h'

lemma sq15T_bounds :
    1.3763 < sq15T ∧ sq15T < 1.3765 ∧ 1.8944 < sq15T ^ 2 ∧ sq15T ^ 2 < 1.8945 ∧
      2.6072 < sq15T ^ 3 ∧ sq15T ^ 3 < 2.6078 := by
  have hq := sq15T_quartic
  have hp := sq15T_pos
  have h1 : 1 < sq15T ^ 2 := by
    rw [sq15T_sq]
    have : 0 < 2 / Real.sqrt 5 := by positivity
    linarith
  have hlo2 : 1.8944 < sq15T ^ 2 := by nlinarith
  have hhi2 : sq15T ^ 2 < 1.8945 := by nlinarith
  have hlo : 1.3763 < sq15T := by nlinarith
  have hhi : sq15T < 1.3765 := by nlinarith
  refine ⟨hlo, hhi, hlo2, hhi2, ?_, ?_⟩
  · have : sq15T ^ 3 = sq15T * sq15T ^ 2 := by ring
    rw [this]; nlinarith
  · have : sq15T ^ 3 = sq15T * sq15T ^ 2 := by ring
    rw [this]; nlinarith

/-- `x`-coordinates of the 15 centres (cubic polynomials in `t = tan 54°`). -/
noncomputable def sq15X : Fin 15 → ℝ := ![1, 1, -1, -1,
  -1 - 15/4 * sq15T + 5/4 * sq15T ^ 3,
  3/4 - 15/4 * sq15T - 5/4 * sq15T ^ 2 + 5/4 * sq15T ^ 3,
  3/4 - 5/4 * sq15T ^ 2,
  3/4 + 25/4 * sq15T - 5/4 * sq15T ^ 2 - 15/4 * sq15T ^ 3,
  25/4 * sq15T - 15/4 * sq15T ^ 3,
  0,
  -25/4 * sq15T + 15/4 * sq15T ^ 3,
  -3/4 - 25/4 * sq15T + 5/4 * sq15T ^ 2 + 15/4 * sq15T ^ 3,
  -3/4 + 5/4 * sq15T ^ 2,
  -3/4 + 15/4 * sq15T + 5/4 * sq15T ^ 2 - 5/4 * sq15T ^ 3,
  1 + 15/4 * sq15T - 5/4 * sq15T ^ 3]

/-- `y`-coordinates of the 15 centres. -/
noncomputable def sq15Y : Fin 15 → ℝ := ![sq15T, 2 + sq15T, 2 + sq15T, sq15T,
  -7/4 + sq15T + 5/4 * sq15T ^ 2,
  -7/4 - 11/4 * sq15T + 5/4 * sq15T ^ 2 + 5/4 * sq15T ^ 3,
  -11/4 * sq15T + 5/4 * sq15T ^ 3,
  3/4 - 11/4 * sq15T - 5/4 * sq15T ^ 2 + 5/4 * sq15T ^ 3,
  3/4 + 7/2 * sq15T - 5/4 * sq15T ^ 2 - 5/2 * sq15T ^ 3,
  7/2 * sq15T - 5/2 * sq15T ^ 3,
  3/4 + 7/2 * sq15T - 5/4 * sq15T ^ 2 - 5/2 * sq15T ^ 3,
  3/4 - 11/4 * sq15T - 5/4 * sq15T ^ 2 + 5/4 * sq15T ^ 3,
  -11/4 * sq15T + 5/4 * sq15T ^ 3,
  -7/4 - 11/4 * sq15T + 5/4 * sq15T ^ 2 + 5/4 * sq15T ^ 3,
  -7/4 + sq15T + 5/4 * sq15T ^ 2]

set_option maxHeartbeats 8000000 in
lemma sq15_sep (i j : Fin 15) (hij : i ≠ j) :
    4 ≤ (sq15X i - sq15X j) ^ 2 + (sq15Y i - sq15Y j) ^ 2 := by
  have h4 := sq15T_quartic
  have h5 : sq15T ^ 5 = 2 * sq15T ^ 3 - sq15T / 5 := by
    rw [show sq15T ^ 5 = sq15T * sq15T ^ 4 by ring, h4]; ring
  have h6 : sq15T ^ 6 = 19 / 5 * sq15T ^ 2 - 2 / 5 := by
    rw [show sq15T ^ 6 = sq15T ^ 2 * sq15T ^ 4 by ring, h4]
    linear_combination (2 : ℝ) * h4
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sq15T_bounds
  fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
    simp only [sq15X, sq15Y, Fin.reduceFinMk, Matrix.cons_val] <;> linarith

lemma sq15_inside (i : Fin 15) :
    sq15X i ^ 2 + sq15Y i ^ 2 ≤ 5 + sq15T ^ 2 + 4 * sq15T := by
  have h4 := sq15T_quartic
  have h5 : sq15T ^ 5 = 2 * sq15T ^ 3 - sq15T / 5 := by
    rw [show sq15T ^ 5 = sq15T * sq15T ^ 4 by ring, h4]; ring
  have h6 : sq15T ^ 6 = 19 / 5 * sq15T ^ 2 - 2 / 5 := by
    rw [show sq15T ^ 6 = sq15T ^ 2 * sq15T ^ 4 by ring, h4]
    linear_combination (2 : ℝ) * h4
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sq15T_bounds
  fin_cases i <;> simp only [sq15X, sq15Y, Fin.reduceFinMk, Matrix.cons_val] <;>
    linarith

lemma sq15_circle_eq (r : ℝ≥0) : Circle r = Metric.ball (0 : ℝ²) r := by
  ext p
  simp only [SquarePacking.Circle, Set.mem_ofPred_eq, mem_ball_zero_iff, EuclideanSpace.norm_eq,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [Real.sqrt_lt (add_nonneg (sq_nonneg _) (sq_nonneg _)) r.coe_nonneg]

/-- The centres as points of the plane. -/
noncomputable def sq15C (i : Fin 15) : ℝ² := !₂[sq15X i, sq15Y i]

lemma sq15C_dist (i j : Fin 15) :
    dist (sq15C i) (sq15C j) = Real.sqrt ((sq15X i - sq15X j) ^ 2 + (sq15Y i - sq15Y j) ^ 2) := by
  simp [sq15C, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem fifteen_circle_packing_in_circle_bound :
    Nonempty (Packing 15 UnitCircle
      (Circle (1 + NNReal.sqrt (6 + 2 / NNReal.sqrt 5 +
        4 * NNReal.sqrt (1 + 2 / NNReal.sqrt 5))))) := by
  have himg : ∀ i, IsometryEquiv.addRight (sq15C i) '' UnitCircle = Metric.ball (sq15C i) 1 := by
    intro i
    rw [UnitCircle, sq15_circle_eq, IsometryEquiv.image_ball]
    simp
  refine ⟨⟨fun i => IsometryEquiv.addRight (sq15C i), ?_, ?_⟩⟩
  · intro i j hij
    simp only [himg]
    apply Metric.ball_disjoint_ball
    rw [sq15C_dist, show (1 : ℝ) + 1 = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num]
    exact Real.sqrt_le_sqrt (sq15_sep i j hij)
  · intro i
    simp only [himg]
    rw [sq15_circle_eq]
    apply Metric.ball_subset_ball'
    have hd : dist (sq15C i) 0 = Real.sqrt (sq15X i ^ 2 + sq15Y i ^ 2) := by
      simp [sq15C, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [hd]
    push_cast
    have h56 : 6 + 2 / Real.sqrt 5 + 4 * Real.sqrt (1 + 2 / Real.sqrt 5) =
        5 + sq15T ^ 2 + 4 * sq15T := by
      rw [sq15T_sq]; unfold sq15T; ring
    rw [h56]
    have := Real.sqrt_le_sqrt (sq15_inside i)
    linarith

end OpenProofs.SquarePacking
