import FormalConjectures.ErdosProblems.«508»

/-!
# `Erdos508.HadwigerNelsonAtMostSeven`

Upstream: `Erdos508.HadwigerNelsonAtMostSeven` (category textbook), `FormalConjectures/ErdosProblems/508.lean` line 105.

Proof idea: tile the plane by half-open bricks of width `4/5` and height `3/5` laid in a brick-wall
pattern (row `j = ⌊5y/3⌋`, brick `i = ⌊5x/4 - j/2⌋`, so consecutive rows are shifted by half a
brick), and colour brick `(i, j)` with `i + 3j` in `ZMod 7`. Two points of one brick are at
distance `< 1` because `(4/5)² + (3/5)² = 1`. For two points at distance exactly `1` the brick
offsets `(a, b)` satisfy `|b| ≤ 2` and `|2a + b| ≤ 4`; together with `7 ∣ a + 3b` this leaves
`(0, 0)` (same brick) and `±(1, 2)`, where the horizontal gap exceeds `4/5` and the vertical gap
exceeds `3/5`, so the distance exceeds `1`.
-/

open SimpleGraph
open scoped EuclideanGeometry
open Erdos508

namespace OpenProofs.Erdos508

/-- Colour of the point `(x, y)` in the brick-wall colouring. -/
noncomputable def brickColor508 (x y : ℝ) : ZMod 7 :=
  ((⌊5 * x / 4 - (⌊5 * y / 3⌋ : ℝ) / 2⌋ + 3 * ⌊5 * y / 3⌋ : ℤ) : ZMod 7)

theorem brickColor508_ne (x0 x1 y0 y1 : ℝ) (h : (x0 - y0) ^ 2 + (x1 - y1) ^ 2 = 1) :
    brickColor508 x0 x1 ≠ brickColor508 y0 y1 := by
  intro heq
  unfold brickColor508 at heq
  set j := ⌊5 * x1 / 3⌋ with hj
  set j' := ⌊5 * y1 / 3⌋ with hj'
  set i := ⌊5 * x0 / 4 - (j : ℝ) / 2⌋ with hi
  set i' := ⌊5 * y0 / 4 - (j' : ℝ) / 2⌋ with hi'
  have hdvd : (7 : ℤ) ∣ (i' + 3 * j') - (i + 3 * j) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp heq
  have hj1 : (j : ℝ) ≤ 5 * x1 / 3 := Int.floor_le _
  have hj2 : 5 * x1 / 3 < j + 1 := Int.lt_floor_add_one _
  have hj'1 : (j' : ℝ) ≤ 5 * y1 / 3 := Int.floor_le _
  have hj'2 : 5 * y1 / 3 < j' + 1 := Int.lt_floor_add_one _
  have hi1 : (i : ℝ) ≤ 5 * x0 / 4 - (j : ℝ) / 2 := Int.floor_le _
  have hi2 : 5 * x0 / 4 - (j : ℝ) / 2 < i + 1 := Int.lt_floor_add_one _
  have hi'1 : (i' : ℝ) ≤ 5 * y0 / 4 - (j' : ℝ) / 2 := Int.floor_le _
  have hi'2 : 5 * y0 / 4 - (j' : ℝ) / 2 < i' + 1 := Int.lt_floor_add_one _
  have e1 : x1 - y1 ≤ 1 := by nlinarith [sq_nonneg (x0 - y0), sq_nonneg (x1 - y1 - 1)]
  have e2 : y1 - x1 ≤ 1 := by nlinarith [sq_nonneg (x0 - y0), sq_nonneg (x1 - y1 + 1)]
  have e3 : x0 - y0 ≤ 1 := by nlinarith [sq_nonneg (x1 - y1), sq_nonneg (x0 - y0 - 1)]
  have e4 : y0 - x0 ≤ 1 := by nlinarith [sq_nonneg (x1 - y1), sq_nonneg (x0 - y0 + 1)]
  have hb1 : j' - j < 3 := by
    have : ((j' - j : ℤ) : ℝ) < 3 := by push_cast; linarith
    exact_mod_cast this
  have hb2 : -3 < j' - j := by
    have : (-3 : ℝ) < ((j' - j : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have ha1 : 2 * (i' - i) + (j' - j) < 5 := by
    have : ((2 * (i' - i) + (j' - j) : ℤ) : ℝ) < 5 := by push_cast; linarith
    exact_mod_cast this
  have ha2 : -5 < 2 * (i' - i) + (j' - j) := by
    have : (-5 : ℝ) < ((2 * (i' - i) + (j' - j) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  clear_value i i' j j'
  have hcases : (i' = i ∧ j' = j) ∨ (i' = i + 1 ∧ j' = j + 2) ∨ (i' = i - 1 ∧ j' = j - 2) := by
    obtain ⟨d, hd⟩ := hdvd
    have hb : j' - j = -2 ∨ j' - j = -1 ∨ j' - j = 0 ∨ j' - j = 1 ∨ j' - j = 2 := by omega
    rcases hb with hb | hb | hb | hb | hb <;> omega
  rcases hcases with ⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩
  · have rA : (i' : ℝ) = i := by exact_mod_cast hA
    have rB : (j' : ℝ) = j := by exact_mod_cast hB
    have f1 : y1 - x1 < 3 / 5 := by linarith
    have f2 : x1 - y1 < 3 / 5 := by linarith
    have f3 : y0 - x0 < 4 / 5 := by linarith
    have f4 : x0 - y0 < 4 / 5 := by linarith
    nlinarith [mul_pos (sub_pos.2 f1) (sub_pos.2 f2), mul_pos (sub_pos.2 f3) (sub_pos.2 f4)]
  · have rA : (i' : ℝ) = i + 1 := by exact_mod_cast hA
    have rB : (j' : ℝ) = j + 2 := by exact_mod_cast hB
    have f1 : 3 / 5 < y1 - x1 := by linarith
    have f3 : 4 / 5 < y0 - x0 := by linarith
    nlinarith [mul_pos (sub_pos.2 f1) (sub_pos.2 f1), mul_pos (sub_pos.2 f3) (sub_pos.2 f3)]
  · have rA : (i' : ℝ) = i - 1 := by exact_mod_cast hA
    have rB : (j' : ℝ) = j - 2 := by exact_mod_cast hB
    have f1 : 3 / 5 < x1 - y1 := by linarith
    have f3 : 4 / 5 < x0 - y0 := by linarith
    nlinarith [mul_pos (sub_pos.2 f1) (sub_pos.2 f1), mul_pos (sub_pos.2 f3) (sub_pos.2 f3)]

theorem HadwigerNelsonAtMostSeven :
    χ(ℝ²) ≤ 7 := by
  let C : (UnitDistancePlaneGraph Set.univ).Coloring (ZMod 7) :=
    Coloring.mk (fun p => brickColor508 (p.1 0) (p.1 1)) (by
      intro p q hpq
      apply brickColor508_ne
      have hd : dist p q = 1 := hpq
      rw [Subtype.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.sqrt_eq_one] at hd
      simpa [Real.dist_eq, sq_abs] using hd)
  have hC := C.colorable
  rw [ZMod.card] at hC
  exact_mod_cast hC.chromaticNumber_le

end OpenProofs.Erdos508
