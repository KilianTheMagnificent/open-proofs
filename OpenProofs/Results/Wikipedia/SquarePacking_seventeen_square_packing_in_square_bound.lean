import FormalConjectures.Wikipedia.SquarePacking

/-!
# `SquarePacking.seventeen_square_packing_in_square_bound`

Upstream: `SquarePacking.seventeen_square_packing_in_square_bound` (category textbook), `FormalConjectures/Wikipedia/SquarePacking.lean` line 132.

Proof idea: an explicit packing, a rational perturbation of John Bidwell's packing of seventeen
unit squares (side `4.6755300936…`). Ten squares are axis-parallel; six are rotated by
`θ ≈ 50.1925°` with the rational point `(cos θ, sin θ) = (2436, 2923) / 3805` on the unit circle
(from `tan (θ / 2) = 37 / 79`), and one is rotated by `φ ≈ 36.6230°` with
`(cos φ, sin φ) = (17955, 13348) / 22373` (from `tan (φ / 2) = 47 / 142`). The translations are
rationals with denominator `10⁵`, chosen by a linear program, so that inside the square of side
`4.6756` every pair of squares and every square and the boundary are separated by a gap of at
least `5 · 10⁻⁶`. Each embedding is the affine isometry `p ↦ (a + c p₀ - s p₁, b + s p₀ + c p₁)`.
Disjointness of two images reduces to the infeasibility of a linear system in the four
unit-square coordinates, and containment to linear bounds; both are closed by `linarith`.
-/

open EuclideanGeometry
open scoped NNReal
open SquarePacking

namespace OpenProofs.SquarePacking

/-- The affine map `p ↦ (a + c p₀ - s p₁, b + s p₀ + c p₁)`, an isometry when `c² + s² = 1`. -/
noncomputable def seventeenSqIso (c s a b : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ℝ² ≃ᵢ ℝ² where
  toFun p := !₂[a + c * p 0 - s * p 1, b + s * p 0 + c * p 1]
  invFun p := !₂[c * (p 0 - a) + s * (p 1 - b), c * (p 1 - b) - s * (p 0 - a)]
  left_inv p := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 0) * h
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 1) * h
  right_inv p := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 0 - a) * h
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination (p 1 - b) * h
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.dist_eq, sq_abs]
    linear_combination ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * h

lemma seventeenSqIso_apply (c s a b : ℝ) (h : c ^ 2 + s ^ 2 = 1) (p : ℝ²) :
    seventeenSqIso c s a b h p = !₂[a + c * p 0 - s * p 1, b + s * p 0 + c * p 1] := rfl

lemma seventeenSq_csA : ((2436 : ℝ) / 3805) ^ 2 + ((2923 : ℝ) / 3805) ^ 2 = 1 := by
  norm_num

lemma seventeenSq_csB : ((17955 : ℝ) / 22373) ^ 2 + ((13348 : ℝ) / 22373) ^ 2 = 1 := by
  norm_num

lemma seventeenSq_10 : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num

/-- An axis-parallel placement with lower-left corner `(a, b)`. -/
noncomputable def seventeenSqAxis (a b : ℝ) : ℝ² ≃ᵢ ℝ² := seventeenSqIso 1 0 a b seventeenSq_10

/-- A placement rotated by `θ ≈ 50.19°` with corner `(a, b)`. -/
noncomputable def seventeenSqTiltA (a b : ℝ) : ℝ² ≃ᵢ ℝ² :=
  seventeenSqIso (2436 / 3805) (2923 / 3805) a b seventeenSq_csA

/-- A placement rotated by `φ ≈ 36.62°` with corner `(a, b)`. -/
noncomputable def seventeenSqTiltB (a b : ℝ) : ℝ² ≃ᵢ ℝ² :=
  seventeenSqIso (17955 / 22373) (13348 / 22373) a b seventeenSq_csB

lemma seventeenSq_disjoint {c s a b c' s' a' b' : ℝ} {h : c ^ 2 + s ^ 2 = 1}
    {h' : c' ^ 2 + s' ^ 2 = 1}
    (H : ∀ x y u v : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → 0 < u → u < 1 → 0 < v → v < 1 →
      a + c * x - s * y = a' + c' * u - s' * v → b + s * x + c * y = b' + s' * u + c' * v →
      False) :
    Disjoint (seventeenSqIso c s a b h '' UnitSquare)
      (seventeenSqIso c' s' a' b' h' '' UnitSquare) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, ⟨hp0, hp1, hp2, hp3⟩, rfl⟩ ⟨q, ⟨hq0, hq1, hq2, hq3⟩, hq⟩
  have e0 := congrArg (· 0) hq
  have e1 := congrArg (· 1) hq
  simp only [seventeenSqIso_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at e0 e1
  exact H _ _ _ _ hp0 hp1 hp2 hp3 hq0 hq1 hq2 hq3 e0.symm e1.symm

lemma seventeenSq_inside {c s a b S : ℝ} {h : c ^ 2 + s ^ 2 = 1}
    (H : ∀ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 →
      0 < a + c * x - s * y ∧ a + c * x - s * y < S ∧ 0 < b + s * x + c * y ∧
        b + s * x + c * y < S) :
    seventeenSqIso c s a b h '' UnitSquare ⊆ Square S := by
  rintro _ ⟨p, ⟨hp0, hp1, hp2, hp3⟩, rfl⟩
  have := H _ _ hp0 hp1 hp2 hp3
  simpa only [Square, Set.mem_ofPred_eq, seventeenSqIso_apply, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using this

/-- The seventeen placements. -/
noncomputable def seventeenSqEmb : Fin 17 → ℝ² ≃ᵢ ℝ² :=
  ![seventeenSqAxis (1 / 100000) (367559 / 100000),
    seventeenSqAxis (50001 / 50000) (367559 / 100000),
    seventeenSqAxis (133779 / 50000) (367559 / 100000),
    seventeenSqAxis (367559 / 100000) (367559 / 100000),
    seventeenSqTiltA (23593 / 10000) (63617 / 25000),
    seventeenSqAxis (1 / 100000) (133779 / 50000),
    seventeenSqAxis (367559 / 100000) (267551 / 100000),
    seventeenSqTiltA (40519 / 25000) (185841 / 100000),
    seventeenSqTiltA (154557 / 50000) (93041 / 50000),
    seventeenSqTiltA (76821 / 100000) (25343 / 20000),
    seventeenSqTiltA (11763 / 5000) (7341 / 6250),
    seventeenSqAxis (367559 / 100000) (156209 / 100000),
    seventeenSqTiltA (30001 / 20000) (5833 / 10000),
    seventeenSqTiltB (157107 / 50000) (60351 / 100000),
    seventeenSqAxis (1 / 100000) (1 / 100000),
    seventeenSqAxis (5773 / 3125) (1 / 100000),
    seventeenSqAxis (367559 / 100000) (1 / 100000)]

set_option maxHeartbeats 4000000 in
lemma seventeenSq_key : ∀ i j : Fin 17, i < j →
    Disjoint (seventeenSqEmb i '' UnitSquare) (seventeenSqEmb j '' UnitSquare) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd hij (by decide)
    | (apply seventeenSq_disjoint
       all_goals first
         | exact seventeenSq_csA
         | exact seventeenSq_csB
         | exact seventeenSq_10
         | (intros; linarith))

set_option maxHeartbeats 1000000 in
lemma seventeenSq_inside_all (i : Fin 17) :
    seventeenSqEmb i '' UnitSquare ⊆ Square (46756 / 10000) := by
  fin_cases i <;>
    (apply seventeenSq_inside
     all_goals first
       | exact seventeenSq_csA
       | exact seventeenSq_csB
       | exact seventeenSq_10
       | (intro x y hx0 hx1 hy0 hy1; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith))

theorem seventeen_square_packing_in_square_bound :
    Nonempty (Packing 17 UnitSquare (Square 4.6756)) := by
  refine ⟨⟨seventeenSqEmb, fun i j hij => ?_, fun i => ?_⟩⟩
  · rcases lt_or_gt_of_ne hij with h | h
    · exact seventeenSq_key i j h
    · exact (seventeenSq_key j i h).symm
  · rw [show (4.6756 : ℝ) = 46756 / 10000 by norm_num]
    exact seventeenSq_inside_all i

end OpenProofs.SquarePacking
