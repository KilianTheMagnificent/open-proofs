import FormalConjectures.ErdosProblems.«91»

/-!
# `Erdos91.erdos_91.test.equiTriangle_unique_optimal`

Upstream: `Erdos91.erdos_91.test.equiTriangle_unique_optimal` (category test), `FormalConjectures/ErdosProblems/91.lean` line 115.
Proof idea: the equilateral triangle realises one distance, so `minimalDistinctDistances ℝ² 3 = 1`
and an optimal `A = {a, b, c}` has all three pairwise distances equal to some `d > 0`. After
swapping `b` and `c` if needed, the orientation `w = u₁v₂ - u₂v₁` of `u = b - a`, `v = c - a` is
nonnegative; from `|u|² = |v|² = |v - u|² = d²` one gets `u·v = d²/2` and `w = (√3/2)d²`. The map
`x ↦ (u·(x - a), u^⊥·(x - a)) / d²` is a bijection of the plane (explicit inverse
`y ↦ a + y₁u + y₂u^⊥`) scaling all distances by `1/d`, and it sends `a, b, c` to
`(0, 0), (1, 0), (1/2, √3/2)`, i.e. onto `equiTriangle`.
-/

open Finset EuclideanGeometry Filter
open Erdos91

namespace OpenProofs.Erdos91

theorem equiTri_dist_sq (x y : ℝ²) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem equiTri_ext (x y : ℝ²) (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem equiTri_exists_dilation (a b c : ℝ²) (d : ℝ) (hd : 0 < d)
    (hab : (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 = d ^ 2)
    (hac : (c 0 - a 0) ^ 2 + (c 1 - a 1) ^ 2 = d ^ 2)
    (hbc : (c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2 = d ^ 2)
    (hw : 0 ≤ (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) :
    ∃ f : ℝ² ≃ᵈ ℝ², f a = !₂[0, 0] ∧ f b = !₂[1, 0] ∧ f c = !₂[1 / 2, Real.sqrt 3 / 2] := by
  obtain ⟨u1, hu1⟩ : ∃ u, u = b 0 - a 0 := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u, u = b 1 - a 1 := ⟨_, rfl⟩
  obtain ⟨v1, hv1⟩ : ∃ v, v = c 0 - a 0 := ⟨_, rfl⟩
  obtain ⟨v2, hv2⟩ : ∃ v, v = c 1 - a 1 := ⟨_, rfl⟩
  have hbc' : (v1 - u1) ^ 2 + (v2 - u2) ^ 2 = d ^ 2 := by
    rw [hu1, hu2, hv1, hv2]; linear_combination hbc
  rw [← hu1, ← hu2] at hab
  rw [← hv1, ← hv2] at hac
  rw [← hu1, ← hu2, ← hv1, ← hv2] at hw
  have hd2 : d ^ 2 ≠ 0 := by positivity
  have hu : u1 ^ 2 + u2 ^ 2 ≠ 0 := by rw [hab]; exact hd2
  let F : ℝ² → ℝ² := fun x =>
    !₂[(u1 * (x 0 - a 0) + u2 * (x 1 - a 1)) / d ^ 2, (-u2 * (x 0 - a 0) + u1 * (x 1 - a 1)) / d ^ 2]
  let G : ℝ² → ℝ² := fun y =>
    !₂[a 0 + u1 * y 0 - u2 * y 1, a 1 + u2 * y 0 + u1 * y 1]
  have hFG : ∀ y, F (G y) = y := by
    intro y
    apply equiTri_ext
    · simp only [F, G]
      simp
      rw [← hab]
      field_simp
      ring
    · simp only [F, G]
      simp
      rw [← hab]
      field_simp
      ring
  have hGF : ∀ x, G (F x) = x := by
    intro x
    apply equiTri_ext
    · simp only [F, G]
      simp
      rw [← hab]
      field_simp
      ring
    · simp only [F, G]
      simp
      rw [← hab]
      field_simp
      ring
  let r : NNReal := ⟨d⁻¹, by positivity⟩
  have hr : (r : ℝ) = d⁻¹ := rfl
  have hr0 : r ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    rw [hr, NNReal.coe_zero] at h'
    exact (inv_ne_zero hd.ne') h'
  have hdist : ∀ x y, dist (F x) (F y) = r * dist x y := by
    intro x y
    rw [hr]
    have h1 : 0 ≤ dist (F x) (F y) := dist_nonneg
    have h2 : 0 ≤ d⁻¹ * dist x y := by positivity
    refine (pow_left_inj₀ h1 h2 two_ne_zero).mp ?_
    rw [mul_pow, inv_pow, equiTri_dist_sq, equiTri_dist_sq]
    simp only [F]
    simp
    rw [← hab]
    field_simp
    ring
  let e : ℝ² ≃ ℝ² := ⟨F, G, hGF, hFG⟩
  let f : ℝ² ≃ᵈ ℝ² :=
    { toEquiv := e
      edist_eq' := (Dilation.mkOfDistEq F ⟨r, hr0, hdist⟩).edist_eq' }
  have hp : u1 * v1 + u2 * v2 = d ^ 2 / 2 := by
    linear_combination (hab + hac - hbc') / 2
  have hw2 : u1 * v2 - u2 * v1 = Real.sqrt 3 / 2 * d ^ 2 := by
    have h3 : 0 ≤ Real.sqrt 3 / 2 * d ^ 2 := by positivity
    refine (pow_left_inj₀ hw h3 two_ne_zero).mp ?_
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
    linear_combination (v1 ^ 2 + v2 ^ 2) * hab + d ^ 2 * hac - (u1 * v1 + u2 * v2 + d ^ 2 / 2) * hp
  refine ⟨f, ?_, ?_, ?_⟩
  · show F a = _
    apply equiTri_ext <;> simp [F]
  · show F b = _
    apply equiTri_ext
    · simp only [F]
      simp
      rw [← hu1, ← hu2]
      field_simp
      linear_combination hab
    · simp only [F]
      simp
      left
      rw [← hu1, ← hu2]
      ring
  · show F c = _
    apply equiTri_ext
    · simp only [F]
      simp
      rw [← hv1, ← hv2]
      field_simp
      linear_combination 2 * hp
    · simp only [F]
      simp
      rw [← hv1, ← hv2]
      field_simp
      linear_combination 2 * hw2

theorem equiTri_distinctDistances : distinctDistances equiTriangle = 1 := by
  unfold distinctDistances distanceSet equiTriangle
  have eucl_dist_one_of_sq : ∀ {x y : ℝ²}, dist x y ^ 2 = 1 → dist x y = 1 := by
    intro x y h; nlinarith [dist_nonneg (x := x) (y := y), sq_nonneg (dist x y)]
  have hd01 : dist (!₂[(0 : ℝ), 0]) (!₂[(1 : ℝ), 0]) = 1 := eucl_dist_one_of_sq <| by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]; simp [Real.dist_eq]
  have hd02 : dist (!₂[(0 : ℝ), 0]) (!₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]) = 1 :=
    eucl_dist_one_of_sq <| by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3,
        sq_abs ((0 : ℝ) - 1 / 2), sq_abs ((0 : ℝ) - Real.sqrt 3 / 2)]
  have hd12 : dist (!₂[(1 : ℝ), 0]) (!₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]) = 1 :=
    eucl_dist_one_of_sq <| by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3,
        sq_abs ((1 : ℝ) - 1 / 2), sq_abs ((0 : ℝ) - Real.sqrt 3 / 2)]
  suffices h : ({!₂[(0 : ℝ), 0], !₂[(1 : ℝ), 0], !₂[(1 : ℝ) / 2, Real.sqrt 3 / 2]} :
      Finset ℝ²).offDiag.image (fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2) = {1} by
    simp only [h, Finset.card_singleton]
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_image.mpr
    ⟨⟨!₂[0, 0], !₂[1, 0]⟩, by simp [Finset.mem_offDiag], hd01⟩, fun d hd => ?_⟩
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton] at hab
  obtain ⟨ha, hb, _⟩ := hab
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> first
    | contradiction | exact hd01 | exact hd02 | exact hd12
    | (rw [dist_comm]; first | exact hd01 | exact hd02 | exact hd12)

theorem erdos_91.test.equiTriangle_unique_optimal :
    ∀ A : Finset ℝ², IsOptimal A 3 → DilationEquivSimilar A equiTriangle := by
  rintro A ⟨hcard, hopt⟩
  have h1 : distinctDistances A = 1 := by
    rw [hopt, ← (Erdos91.erdos_91.test.equiTriangle_optimal).2, equiTri_distinctDistances]
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h1
  have hmem : ∀ x ∈ ({a, b, c} : Finset ℝ²), ∀ y ∈ ({a, b, c} : Finset ℝ²), x ≠ y →
      dist x y = d := by
    intro x hx y hy hxy
    have : dist x y ∈ distanceSet ({a, b, c} : Finset ℝ²) :=
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
    rw [hd] at this
    simpa using this
  have dab : dist b a = d := hmem b (by simp) a (by simp) hab.symm
  have dac : dist c a = d := hmem c (by simp) a (by simp) hac.symm
  have dbc : dist c b = d := hmem c (by simp) b (by simp) hbc.symm
  have hd0 : 0 < d := dab ▸ dist_pos.mpr hab.symm
  have hab' := equiTri_dist_sq b a
  have hac' := equiTri_dist_sq c a
  have hbc' := equiTri_dist_sq c b
  rw [dab] at hab'
  rw [dac] at hac'
  rw [dbc] at hbc'
  rcases le_total 0 ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) with hw | hw
  · obtain ⟨f, hfa, hfb, hfc⟩ := equiTri_exists_dilation a b c d hd0 hab'.symm hac'.symm
      hbc'.symm hw
    refine ⟨f, ?_⟩
    rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_insert_eq, Set.image_singleton, hfa, hfb, hfc]
    simp [equiTriangle]
  · obtain ⟨f, hfa, hfc, hfb⟩ := equiTri_exists_dilation a c b d hd0 hac'.symm hab'.symm
      (by linear_combination hbc'.symm) (by linarith)
    refine ⟨f, ?_⟩
    rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_insert_eq, Set.image_singleton, hfa, hfb, hfc, Set.pair_comm]
    simp [equiTriangle]

end OpenProofs.Erdos91
