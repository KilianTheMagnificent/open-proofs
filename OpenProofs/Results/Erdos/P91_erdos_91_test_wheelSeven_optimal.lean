import FormalConjectures.ErdosProblems.«91»
import OpenProofs.Results.Erdos.P91_erdos_91_test_circleSeven_optimal

/-!
# `Erdos91.erdos_91.test.wheelSeven_optimal`

Upstream: `Erdos91.erdos_91.test.wheelSeven_optimal` (category test), `FormalConjectures/ErdosProblems/91.lean` line 128.
Proof idea: the seven points (centre plus regular unit hexagon) are pairwise distinct, and every
squared distance between two of them is `1`, `3` or `4`, so the distances lie in `{1, √3, 2}` and
there are at most three. The lower bound "every 7-point set has at least 3 distances" is
`OpenProofs.Erdos91.circSeven_three_le` (Blokhuis' polynomial method, proved for
`circleSeven_optimal`), which also gives `minimalDistinctDistances ℝ² 7 = 3`.
-/

open Finset EuclideanGeometry Filter
open Erdos91

namespace OpenProofs.Erdos91

theorem wheelSev_dist (a b c d : ℝ) :
    dist (!₂[a, b]) (!₂[c, d]) = √((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem wheelSev_eq_iff (a b c d : ℝ) : (!₂[a, b] = !₂[c, d]) ↔ a = c ∧ b = d := by
  constructor
  · intro e
    exact ⟨by simpa using congrArg (fun p : ℝ² => p 0) e,
      by simpa using congrArg (fun p : ℝ² => p 1) e⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem wheelSev_card : #wheelSeven = 7 := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have h3' : Real.sqrt 3 / 2 ≠ Real.sqrt 3 := by intro h; apply h3; linarith
  have h3'' : Real.sqrt 3 / 2 ≠ 0 := by positivity
  rw [wheelSeven]
  repeat rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, wheelSev_eq_iff, not_or]
    norm_num [h3, h3', h3'', h3'.symm, h3''.symm, Ne.symm h3])]
  rfl

theorem wheelSev_distanceSet_sub : distanceSet wheelSeven ⊆ {1, √3, 2} := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have k1 : ∀ s : ℝ, s = 1 → √s = 1 := by rintro s rfl; simp
  have k3 : ∀ s : ℝ, s = 3 → √s = √3 := by rintro s rfl; rfl
  have k4 : ∀ s : ℝ, s = 4 → √s = 2 := by
    rintro s rfl
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  intro d hd
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  rw [Finset.mem_offDiag] at hab
  obtain ⟨ha, hb, hne⟩ := hab
  simp only [wheelSeven, Finset.mem_insert, Finset.mem_singleton] at ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | exact absurd rfl hne
  | (rw [wheelSev_dist]; first
      | exact Or.inl (k1 _ (by linarith [hs]))
      | exact Or.inr (Or.inl (k3 _ (by linarith [hs])))
      | exact Or.inr (Or.inr (k4 _ (by linarith [hs]))))

theorem erdos_91.test.wheelSeven_optimal : IsOptimal wheelSeven 7 := by
  have hcard : #wheelSeven = 7 := wheelSev_card
  have hle : distinctDistances wheelSeven ≤ 3 :=
    (Finset.card_le_card wheelSev_distanceSet_sub).trans Finset.card_le_three
  have hdist : distinctDistances wheelSeven = 3 :=
    le_antisymm hle (circSeven_three_le wheelSeven hcard)
  refine ⟨hcard, ?_⟩
  rw [hdist]
  unfold minimalDistinctDistances
  apply le_antisymm
  · exact le_csInf ⟨3, wheelSeven, hcard, hdist⟩ fun m ⟨pts, hp, hm⟩ =>
      hm ▸ circSeven_three_le pts hp
  · exact Nat.sInf_le ⟨wheelSeven, hcard, hdist⟩

end OpenProofs.Erdos91
