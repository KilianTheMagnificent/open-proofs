import FormalConjectures.Wikipedia.SquarePacking

/-!
# `SquarePacking.eleven_square_packing_in_square_bound`

Upstream: `SquarePacking.eleven_square_packing_in_square_bound` (category textbook), `FormalConjectures/Wikipedia/SquarePacking.lean` line 109.

Proof idea: an explicit packing, a rational perturbation of Walter Trump's 1979 packing of
eleven unit squares (side `3.87708359…`). Six squares are axis-parallel; five are rotated by the
angle `θ ≈ 40.18°` with the rational point `(cos θ, sin θ) = (5855599, 4945200) / 7664401` on the
unit circle (from `tan (θ / 2) = 951 / 2600`). The translations are rationals chosen by a linear
program so that, inside the square of side `3.877084`, every pair of squares and every square and
the boundary are separated by a gap of about `8 · 10⁻⁸`. Each embedding is the affine isometry
`p ↦ (a + c p₀ - s p₁, b + s p₀ + c p₁)`. Disjointness of two images reduces to the infeasibility
of a linear system in the four unit-square coordinates, and containment to linear bounds; both
are closed by `linarith`.
-/

open EuclideanGeometry
open scoped NNReal
open SquarePacking

namespace OpenProofs.SquarePacking

/-- The affine map `p ↦ (a + c p₀ - s p₁, b + s p₀ + c p₁)`, an isometry when `c² + s² = 1`. -/
noncomputable def elevenSqIso (c s a b : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ℝ² ≃ᵢ ℝ² where
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

lemma elevenSqIso_apply (c s a b : ℝ) (h : c ^ 2 + s ^ 2 = 1) (p : ℝ²) :
    elevenSqIso c s a b h p = !₂[a + c * p 0 - s * p 1, b + s * p 0 + c * p 1] := rfl

lemma elevenSq_cs : ((5855599 : ℝ) / 7664401) ^ 2 + ((4945200 : ℝ) / 7664401) ^ 2 = 1 := by
  norm_num

lemma elevenSq_10 : (1 : ℝ) ^ 2 + 0 ^ 2 = 1 := by norm_num

/-- An axis-parallel placement with lower-left corner `(a, b)`. -/
noncomputable def elevenSqAxis (a b : ℝ) : ℝ² ≃ᵢ ℝ² := elevenSqIso 1 0 a b elevenSq_10

/-- A placement rotated by `θ ≈ 40.18°` with corner `(a, b)`. -/
noncomputable def elevenSqTilt (a b : ℝ) : ℝ² ≃ᵢ ℝ² :=
  elevenSqIso (5855599 / 7664401) (4945200 / 7664401) a b elevenSq_cs

lemma elevenSq_disjoint {c s a b c' s' a' b' : ℝ} {h : c ^ 2 + s ^ 2 = 1}
    {h' : c' ^ 2 + s' ^ 2 = 1}
    (H : ∀ x y u v : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → 0 < u → u < 1 → 0 < v → v < 1 →
      a + c * x - s * y = a' + c' * u - s' * v → b + s * x + c * y = b' + s' * u + c' * v →
      False) :
    Disjoint (elevenSqIso c s a b h '' UnitSquare) (elevenSqIso c' s' a' b' h' '' UnitSquare) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, ⟨hp0, hp1, hp2, hp3⟩, rfl⟩ ⟨q, ⟨hq0, hq1, hq2, hq3⟩, hq⟩
  have e0 := congrArg (· 0) hq
  have e1 := congrArg (· 1) hq
  simp only [elevenSqIso_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at e0 e1
  exact H _ _ _ _ hp0 hp1 hp2 hp3 hq0 hq1 hq2 hq3 e0.symm e1.symm

lemma elevenSq_inside {c s a b S : ℝ} {h : c ^ 2 + s ^ 2 = 1}
    (H : ∀ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 →
      0 < a + c * x - s * y ∧ a + c * x - s * y < S ∧ 0 < b + s * x + c * y ∧
        b + s * x + c * y < S) :
    elevenSqIso c s a b h '' UnitSquare ⊆ Square S := by
  rintro _ ⟨p, ⟨hp0, hp1, hp2, hp3⟩, rfl⟩
  have := H _ _ hp0 hp1 hp2 hp3
  simpa only [Square, Set.mem_ofPred_eq, elevenSqIso_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using this

/-- The eleven placements. -/
noncomputable def elevenSqEmb : Fin 11 → ℝ² ≃ᵢ ℝ² :=
  ![elevenSqAxis (9 / 100000000) (9 / 100000000),
    elevenSqAxis (9 / 100000000) (187708383 / 100000000),
    elevenSqAxis (9 / 100000000) (287708391 / 100000000),
    elevenSqAxis (100000017 / 100000000) (287708391 / 100000000),
    elevenSqAxis (203255867 / 100000000) (287708391 / 100000000),
    elevenSqTilt (190022161 / 100000000) (148391703 / 100000000),
    elevenSqTilt (15160783 / 12500000) (3739751 / 5000000),
    elevenSqTilt (37541673 / 20000000) (9 / 100000000),
    elevenSqTilt (128222131 / 50000000) (18399173 / 25000000),
    elevenSqTilt (62261687 / 20000000) (5113089 / 3125000),
    elevenSqAxis (287708391 / 100000000) (9 / 100000000)]

theorem eleven_square_packing_in_square_bound :
    Nonempty (Packing 11 UnitSquare (Square 3.877084)) := by
  have key : ∀ i j : Fin 11, i < j →
      Disjoint (elevenSqEmb i '' UnitSquare) (elevenSqEmb j '' UnitSquare) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | (apply elevenSq_disjoint
         all_goals first | exact elevenSq_cs | exact elevenSq_10 | (intros; linarith))
  refine ⟨⟨elevenSqEmb, fun i j hij => ?_, fun i => ?_⟩⟩
  · rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  · rw [show (3.877084 : ℝ) = 3877084 / 1000000 by norm_num]
    fin_cases i <;>
      (apply elevenSq_inside
       all_goals first
         | exact elevenSq_cs
         | exact elevenSq_10
         | (intro x y hx0 hx1 hy0 hy1; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith))

end OpenProofs.SquarePacking
