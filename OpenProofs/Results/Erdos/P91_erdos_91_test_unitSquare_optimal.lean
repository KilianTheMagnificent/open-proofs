import FormalConjectures.ErdosProblems.«91»

/-!
# `Erdos91.erdos_91.test.unitSquare_optimal`

Upstream: `Erdos91.erdos_91.test.unitSquare_optimal` (category test), `FormalConjectures/ErdosProblems/91.lean` line 120.
Proof idea: the square's distance set is `{1, √2}` (check all ordered pairs), so it has 2
distinct distances. For the lower bound, 4 points with a single distance `d` would give vectors
`u, v, w` (from one point to the others) with `|u|² = |v|² = |w|² = d²` and pairwise inner
products `d²/2`. The Gram determinant of three vectors in `ℝ²` vanishes identically (a `ring`
identity in coordinates), while these values make it `d⁶/2`, forcing `d = 0`, contradicting
distinctness.
-/

open Finset EuclideanGeometry Filter
open Erdos91

namespace OpenProofs.Erdos91

theorem unitSquare_dist_sq_coords (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem unitSquare_no_four_equidistant (a b c e : ℝ²) (D : ℝ)
    (h1 : dist a b ^ 2 = D) (h2 : dist a c ^ 2 = D) (h3 : dist a e ^ 2 = D)
    (h4 : dist b c ^ 2 = D) (h5 : dist b e ^ 2 = D) (h6 : dist c e ^ 2 = D) : D = 0 := by
  rw [unitSquare_dist_sq_coords] at h1 h2 h3 h4 h5 h6
  set u1 := b 0 - a 0
  set u2 := b 1 - a 1
  set v1 := c 0 - a 0
  set v2 := c 1 - a 1
  set w1 := e 0 - a 0
  set w2 := e 1 - a 1
  have hP : u1 ^ 2 + u2 ^ 2 = D := by linear_combination h1
  have hQ : v1 ^ 2 + v2 ^ 2 = D := by linear_combination h2
  have hR : w1 ^ 2 + w2 ^ 2 = D := by linear_combination h3
  have hS : u1 * v1 + u2 * v2 = D / 2 := by linear_combination (h1 + h2 - h4) / 2
  have hT : w1 * u1 + w2 * u2 = D / 2 := by linear_combination (h1 + h3 - h5) / 2
  have hU : w1 * v1 + w2 * v2 = D / 2 := by linear_combination (h2 + h3 - h6) / 2
  have key : ((u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) - (u1 * v1 + u2 * v2) ^ 2) * (w1 ^ 2 + w2 ^ 2)
      - (w1 * u1 + w2 * u2) ^ 2 * (v1 ^ 2 + v2 ^ 2) - (w1 * v1 + w2 * v2) ^ 2 * (u1 ^ 2 + u2 ^ 2)
      + 2 * (w1 * u1 + w2 * u2) * (w1 * v1 + w2 * v2) * (u1 * v1 + u2 * v2) = 0 := by ring
  rw [hP, hQ, hR, hS, hT, hU] at key
  have hD3 : D ^ 3 = 0 := by linear_combination 2 * key
  exact pow_eq_zero_iff (by norm_num) |>.mp hD3

theorem unitSquare_dist (p q r s : ℝ) :
    dist (!₂[p, q]) (!₂[r, s]) = √((p - r) ^ 2 + (q - s) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  simp

theorem unitSquare_distanceSet : distanceSet unitSquare = {1, √2} := by
  unfold distanceSet unitSquare
  ext d
  simp only [Finset.mem_image, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton,
    Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, rfl⟩
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp_all [unitSquare_dist] <;> norm_num
  · rintro (rfl | rfl)
    · exact ⟨!₂[0, 0], !₂[0, 1], ⟨by simp, by simp, by simp⟩, by simp [unitSquare_dist]⟩
    · exact ⟨!₂[0, 0], !₂[1, 1], ⟨by simp, by simp, by simp⟩, by simp [unitSquare_dist]; norm_num⟩

theorem erdos_91.test.unitSquare_optimal : IsOptimal unitSquare 4 := by
  have hcard : unitSquare.card = 4 := by
    simp [unitSquare]
  have hdist : distinctDistances unitSquare = 2 := by
    unfold distinctDistances
    rw [unitSquare_distanceSet, Finset.card_pair]
    intro h
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    rw [← h] at h2
    norm_num at h2
  have hmin : minimalDistinctDistances ℝ² 4 = 2 := by
    unfold minimalDistinctDistances
    apply le_antisymm
    · exact Nat.sInf_le ⟨unitSquare, hcard, hdist⟩
    · apply le_csInf
      · exact ⟨_, unitSquare, hcard, rfl⟩
      rintro m ⟨points, hcard', rfl⟩
      by_contra hlt
      replace hlt := not_le.mp hlt
      obtain ⟨a, b, c, e, hab, hac, hae, hbc, hbe, hce, rfl⟩ := Finset.card_eq_four.mp hcard'
      have hone : (distanceSet ({a, b, c, e} : Finset ℝ²)).card ≤ 1 := by
        unfold distinctDistances at hlt; omega
      have hmem : ∀ x ∈ ({a, b, c, e} : Finset ℝ²), ∀ y ∈ ({a, b, c, e} : Finset ℝ²), x ≠ y →
          dist x y ∈ distanceSet ({a, b, c, e} : Finset ℝ²) := by
        intro x hx y hy hxy
        exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
      have heq : ∀ x ∈ ({a, b, c, e} : Finset ℝ²), ∀ y ∈ ({a, b, c, e} : Finset ℝ²), x ≠ y →
          dist x y = dist a b := by
        intro x hx y hy hxy
        exact Finset.card_le_one.mp hone _ (hmem x hx y hy hxy) _
          (hmem a (by simp) b (by simp) hab)
      have hD := unitSquare_no_four_equidistant a b c e (dist a b ^ 2) rfl
        (by rw [heq a (by simp) c (by simp) hac])
        (by rw [heq a (by simp) e (by simp) hae])
        (by rw [heq b (by simp) c (by simp) hbc])
        (by rw [heq b (by simp) e (by simp) hbe])
        (by rw [heq c (by simp) e (by simp) hce])
      have : 0 < dist a b := dist_pos.mpr hab
      have : 0 < dist a b ^ 2 := by positivity
      linarith
  exact ⟨hcard, by rw [hdist, hmin]⟩

end OpenProofs.Erdos91
