import FormalConjectures.ErdosProblems.«91»

/-!
# `Erdos91.erdos_91.test.circleSeven_optimal`

Upstream: `Erdos91.erdos_91.test.circleSeven_optimal` (category test), `FormalConjectures/ErdosProblems/91.lean` line 124.
Proof idea: upper bound: the vertices of the regular 7-gon are pairwise distinct and the
squared distance of vertices `k, l` is `2 r² (1 - cos (2π(k-l)/7))`, which takes only the three
values for `|k - l| ∈ {1, 2, 3}` (mod 7). Lower bound (Blokhuis' polynomial method): if seven
points `pᵢ` of the plane had squared distances in `{α, β}` (`α, β ≠ 0`), the quartics
`fᵢ(x) = (|x - pᵢ|² - α)(|x - pᵢ|² - β)` together with `1, x₁, x₂` would be ten linearly
independent vectors in the 9-dimensional span of `|x|⁴, |x|²x₁, |x|²x₂, x₁², x₁x₂, x₂², x₁, x₂, 1`
(independence: evaluate at `p_k`, use the `|x|⁴` and `|x|²xᵢ` coefficients, get `Σ cₖ² = 0`).
So every 7-point set has at least 3 distances, and the minimum for `n = 7` is 3.
-/

open Finset EuclideanGeometry Filter
open Erdos91

namespace OpenProofs.Erdos91

/-- A vanishing linear combination of vectors in `ℝ⁹` stays zero after pairing with a weight. -/
theorem circSeven_aux_comb {ι : Type*} [Fintype ι] (g : ι → Fin 9 → ℝ) (c : ι → ℝ)
    (hc : ∑ i, c i • g i = 0) (wt : Fin 9 → ℝ) : ∑ i, c i * ∑ m, wt m * g i m = 0 := by
  have h : ∀ m, ∑ i, c i * g i m = 0 := fun m => by
    simpa [Finset.sum_apply] using congrFun hc m
  calc ∑ i, c i * ∑ m, wt m * g i m = ∑ m, wt m * ∑ i, c i * g i m := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by simp [h]

/-- Blokhuis' polynomial method in the plane: there are no seven points whose pairwise squared
distances all lie in `{α, β}` with `α, β ≠ 0`. -/
theorem circSeven_no_seven (x y : Fin 7 → ℝ) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h : ∀ i j, i ≠ j →
      ((x i - x j) ^ 2 + (y i - y j) ^ 2 - α) * ((x i - x j) ^ 2 + (y i - y j) ^ 2 - β) = 0) :
    False := by
  set v : Fin 7 → Fin 9 → ℝ := fun i =>
    ![1, -4 * x i, -4 * y i, (2 * (x i ^ 2 + y i ^ 2) - α - β) + 4 * x i ^ 2, 8 * x i * y i,
      (2 * (x i ^ 2 + y i ^ 2) - α - β) + 4 * y i ^ 2,
      -2 * (2 * (x i ^ 2 + y i ^ 2) - α - β) * x i, -2 * (2 * (x i ^ 2 + y i ^ 2) - α - β) * y i,
      (x i ^ 2 + y i ^ 2 - α) * (x i ^ 2 + y i ^ 2 - β)] with hv
  set w : Fin 3 → Fin 9 → ℝ := ![Pi.single 8 1, Pi.single 6 1, Pi.single 7 1] with hw
  have hli : LinearIndependent ℝ (Sum.elim v w) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hco : ∀ m, ∑ i, c (Sum.inl i) * v i m + ∑ j, c (Sum.inr j) * w j m = 0 := by
      intro m
      have := congrFun hc m
      simpa [Finset.sum_apply, Fintype.sum_sum_type] using this
    have key := fun wt => circSeven_aux_comb _ c hc wt
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at key
    have h0 := hco 0
    have h1 := hco 1
    have h2 := hco 2
    simp [hv, hw, Fin.sum_univ_three] at h0 h1 h2
    have hk : ∀ k, c (Sum.inl k) * (α * β) +
        (c (Sum.inr 0) + c (Sum.inr 1) * x k + c (Sum.inr 2) * y k) = 0 := by
      intro k
      have hkey := key ![(x k ^ 2 + y k ^ 2) ^ 2, (x k ^ 2 + y k ^ 2) * x k,
        (x k ^ 2 + y k ^ 2) * y k, x k ^ 2, x k * y k, y k ^ 2, x k, y k, 1]
      have hF : ∀ i, ∑ m, ![(x k ^ 2 + y k ^ 2) ^ 2, (x k ^ 2 + y k ^ 2) * x k,
          (x k ^ 2 + y k ^ 2) * y k, x k ^ 2, x k * y k, y k ^ 2, x k, y k, 1] m * v i m =
          ((x k - x i) ^ 2 + (y k - y i) ^ 2 - α) * ((x k - x i) ^ 2 + (y k - y i) ^ 2 - β) := by
        intro i
        simp [hv, Fin.sum_univ_succ]
        ring
      simp only [hF] at hkey
      rw [Finset.sum_eq_single k (fun i _ hik => by rw [h k i (Ne.symm hik), mul_zero])
        (by simp)] at hkey
      simp [hw, Fin.sum_univ_succ] at hkey
      linear_combination hkey
    have hsq : ∑ k, c (Sum.inl k) ^ 2 = 0 := by
      have hs : ∑ k, c (Sum.inl k) * (c (Sum.inl k) * (α * β) +
          (c (Sum.inr 0) + c (Sum.inr 1) * x k + c (Sum.inr 2) * y k)) = 0 := by
        simp [hk]
      refine (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero hα hβ)
      simp only [Fin.sum_univ_seven] at hs h0 h1 h2 ⊢
      linear_combination hs - c (Sum.inr 0) * h0 - c (Sum.inr 1) / 4 * h1 -
        c (Sum.inr 2) / 4 * h2
    have hz : ∀ k, c (Sum.inl k) = 0 := fun k =>
      (pow_eq_zero_iff two_ne_zero).mp
        ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hsq k (Finset.mem_univ _))
    have e0 := hco 8
    have e1 := hco 6
    have e2 := hco 7
    simp [hz, hw, Fin.sum_univ_three] at e0 e1 e2
    rintro (i | j)
    · exact hz i
    · fin_cases j
      · simpa using e0
      · simpa using e1
      · simpa using e2
  have := hli.fintype_card_le_finrank
  simp at this

/-- Seven points of the plane determine at least three distinct distances. -/
theorem circSeven_three_le (points : Finset ℝ²) (hcard : #points = 7) :
    3 ≤ distinctDistances points := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hpos : ∀ d ∈ distanceSet points, d ≠ 0 := by
    intro d hd
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
    rw [Finset.mem_offDiag] at hab
    exact dist_ne_zero.mpr hab.2.2
  obtain ⟨d1, d2, hd1, hd2, hsub⟩ : ∃ d1 d2 : ℝ, d1 ≠ 0 ∧ d2 ≠ 0 ∧
      ∀ d ∈ distanceSet points, d = d1 ∨ d = d2 := by
    have hD : #(distanceSet points) ≤ 2 := by
      unfold distinctDistances at hlt
      omega
    rcases (by omega : #(distanceSet points) = 0 ∨ #(distanceSet points) = 1 ∨
        #(distanceSet points) = 2) with h | h | h
    · exact ⟨1, 1, one_ne_zero, one_ne_zero, by simp [Finset.card_eq_zero.mp h]⟩
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      exact ⟨a, a, hpos a (by simp [ha]), hpos a (by simp [ha]), by simp [ha]⟩
    · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp h
      exact ⟨a, b, hpos a (by simp [hab]), hpos b (by simp [hab]), by simp [hab]⟩
  let e := (Finset.equivFinOfCardEq hcard).symm
  let p : Fin 7 → ℝ² := fun i => (e i : ℝ²)
  apply circSeven_no_seven (fun i => p i 0) (fun i => p i 1) (d1 ^ 2) (d2 ^ 2)
    (pow_ne_zero 2 hd1) (pow_ne_zero 2 hd2)
  intro i j hij
  have hmem : dist (p i) (p j) ∈ distanceSet points :=
    Finset.mem_image.mpr ⟨(p i, p j), Finset.mem_offDiag.mpr
      ⟨(e i).2, (e j).2, fun h => hij (e.injective (Subtype.ext h))⟩, rfl⟩
  have hsq : dist (p i) (p j) ^ 2 = (p i 0 - p j 0) ^ 2 + (p i 1 - p j 1) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  simp only
  rw [← hsq]
  rcases hsub _ hmem with h | h <;> rw [h] <;> ring

theorem circSeven_dist_sq (r cx cy a b : ℝ) :
    dist (!₂[r * Real.cos a + cx, r * Real.sin a + cy])
      (!₂[r * Real.cos b + cx, r * Real.sin b + cy]) ^ 2 = 2 * r ^ 2 * (1 - Real.cos (a - b)) := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.cos_sub]
  linear_combination r ^ 2 * Real.sin_sq_add_cos_sq a + r ^ 2 * Real.sin_sq_add_cos_sq b

theorem circSeven_cos_cases (k l : ℕ) (hk : k < 7) (hl : l < 7) (hkl : k ≠ l) :
    Real.cos (2 * Real.pi * k / 7 - 2 * Real.pi * l / 7) = Real.cos (2 * Real.pi * 1 / 7) ∨
    Real.cos (2 * Real.pi * k / 7 - 2 * Real.pi * l / 7) = Real.cos (2 * Real.pi * 2 / 7) ∨
    Real.cos (2 * Real.pi * k / 7 - 2 * Real.pi * l / 7) = Real.cos (2 * Real.pi * 3 / 7) := by
  have hd : ∀ d : ℕ, 1 ≤ d → d ≤ 6 →
      Real.cos (2 * Real.pi * d / 7) = Real.cos (2 * Real.pi * 1 / 7) ∨
      Real.cos (2 * Real.pi * d / 7) = Real.cos (2 * Real.pi * 2 / 7) ∨
      Real.cos (2 * Real.pi * d / 7) = Real.cos (2 * Real.pi * 3 / 7) := by
    intro d h1 h6
    interval_cases d
    · left; norm_num
    · right; left; norm_num
    · right; right; norm_num
    · right; right
      rw [show (2 : ℝ) * Real.pi * ((4 : ℕ) : ℝ) / 7 = 2 * Real.pi - 2 * Real.pi * 3 / 7 by
        push_cast; ring, Real.cos_two_pi_sub]
    · right; left
      rw [show (2 : ℝ) * Real.pi * ((5 : ℕ) : ℝ) / 7 = 2 * Real.pi - 2 * Real.pi * 2 / 7 by
        push_cast; ring, Real.cos_two_pi_sub]
    · left
      rw [show (2 : ℝ) * Real.pi * ((6 : ℕ) : ℝ) / 7 = 2 * Real.pi - 2 * Real.pi * 1 / 7 by
        push_cast; ring, Real.cos_two_pi_sub]
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [← Real.cos_neg, neg_sub, show (2 : ℝ) * Real.pi * ((k + d + 1 : ℕ) : ℝ) / 7 -
      2 * Real.pi * (k : ℝ) / 7 = 2 * Real.pi * ((d + 1 : ℕ) : ℝ) / 7 by push_cast; ring]
    exact hd (d + 1) (by omega) (by omega)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    rw [show (2 : ℝ) * Real.pi * ((l + d + 1 : ℕ) : ℝ) / 7 -
      2 * Real.pi * (l : ℝ) / 7 = 2 * Real.pi * ((d + 1 : ℕ) : ℝ) / 7 by push_cast; ring]
    exact hd (d + 1) (by omega) (by omega)

theorem circSeven_cos_lt_one (m : ℝ) (h0 : 0 < m) (h3 : m ≤ 3) :
    Real.cos (2 * Real.pi * m / 7) < 1 := by
  have hpi := Real.pi_pos
  rw [← Real.cos_zero]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by nlinarith) (by positivity)

theorem circSeven_distanceSet_sub (r cx cy : ℝ) :
    distanceSet ((range 7).image fun k : ℕ =>
      !₂[r * Real.cos (2 * Real.pi * k / 7) + cx, r * Real.sin (2 * Real.pi * k / 7) + cy]) ⊆
    {√(2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * 1 / 7))),
      √(2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * 2 / 7))),
      √(2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * 3 / 7)))} := by
  intro d hd
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  rw [Finset.mem_offDiag] at hab
  obtain ⟨ha, hb, hne⟩ := hab
  simp only [Finset.mem_image, Finset.mem_range] at ha hb
  obtain ⟨k, hk, rfl⟩ := ha
  obtain ⟨l, hl, rfl⟩ := hb
  have hkl : k ≠ l := by rintro rfl; exact hne rfl
  rw [← Real.sqrt_sq dist_nonneg, circSeven_dist_sq]
  rcases circSeven_cos_cases k l hk hl hkl with h | h | h <;> rw [h] <;> simp

theorem circSeven_card (r cx cy : ℝ) (hr : r ≠ 0) :
    #((range 7).image fun k : ℕ =>
      !₂[r * Real.cos (2 * Real.pi * k / 7) + cx, r * Real.sin (2 * Real.pi * k / 7) + cy]) = 7 := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro k hk l hl hkl
  by_contra hne
  have h := circSeven_dist_sq r cx cy (2 * Real.pi * k / 7) (2 * Real.pi * l / 7)
  simp only at hkl
  rw [hkl, dist_self] at h
  have hr2 : 0 < r ^ 2 := by positivity
  have hc : Real.cos (2 * Real.pi * k / 7 - 2 * Real.pi * l / 7) < 1 := by
    rcases circSeven_cos_cases k l (by simpa using hk) (by simpa using hl) hne with h' | h' | h' <;>
      rw [h'] <;> exact circSeven_cos_lt_one _ (by norm_num) (by norm_num)
  nlinarith

theorem erdos_91.test.circleSeven_optimal : IsOptimal circleSeven 7 := by
  have hs : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hr : 1 / (2 * Real.sin (Real.pi / 7)) ≠ 0 := by positivity
  have hcard : #circleSeven = 7 := circSeven_card _ _ _ hr
  have hle : distinctDistances circleSeven ≤ 3 :=
    (Finset.card_le_card (circSeven_distanceSet_sub _ _ _)).trans Finset.card_le_three
  have hdist : distinctDistances circleSeven = 3 :=
    le_antisymm hle (circSeven_three_le circleSeven hcard)
  refine ⟨hcard, ?_⟩
  rw [hdist]
  unfold minimalDistinctDistances
  apply le_antisymm
  · exact le_csInf ⟨3, circleSeven, hcard, hdist⟩ fun m ⟨pts, hp, hm⟩ =>
      hm ▸ circSeven_three_le pts hp
  · exact Nat.sInf_le ⟨circleSeven, hcard, hdist⟩

end OpenProofs.Erdos91
