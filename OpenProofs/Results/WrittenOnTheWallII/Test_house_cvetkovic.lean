import FormalConjectures.WrittenOnTheWallII.Test

/-!
# `WrittenOnTheWallII.Test.house_cvetkovic`

Upstream: `WrittenOnTheWallII.Test.house_cvetkovic` (category test), `FormalConjectures/WrittenOnTheWallII/Test.lean` line 185.
Proof idea: the characteristic matrix of the house graph's adjacency matrix is written out
entrywise and Laplace expansion along the first row gives the characteristic polynomial
`X^5 - 6X^3 - 2X^2 + 4X = X (X + 2) (X^3 - 2X^2 - 2X + 2)`. The cubic factor changes sign on
`(-2, -1)`, `(0, 1)` and `(2, 3)`, so the intermediate value theorem gives roots `a < 0 < b < c`
there. The five distinct numbers `0, -2, a, b, c` are roots of a degree-5 polynomial, so they
are its whole root multiset: one zero, two positive and two negative eigenvalues, hence
`cvetkovic HouseGraph = 1 + min 2 2 = 3`.
-/

open SimpleGraph Polynomial
open WrittenOnTheWallII.Test

namespace OpenProofs.WrittenOnTheWallII.Test

theorem house_charmatrix_wow : Matrix.charmatrix (HouseGraph.adjMatrix ℝ) =
    !![X, -1, 0, -1, 0;
       -1, X, -1, 0, 0;
       0, -1, X, -1, -1;
       -1, 0, -1, X, -1;
       0, 0, -1, -1, X] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp +decide [adjMatrix_apply]

theorem house_charpoly_wow : Matrix.charpoly (HouseGraph.adjMatrix ℝ) =
    X ^ 5 - 6 * X ^ 3 - 2 * X ^ 2 + 4 * X := by
  rw [Matrix.charpoly, house_charmatrix_wow]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem house_cvetkovic : cvetkovic HouseGraph = 3 := by
  have hf : Continuous (fun x : ℝ => x ^ 3 - 2 * x ^ 2 - 2 * x + 2) := by fun_prop
  obtain ⟨a, ⟨ha1, ha2⟩, ha⟩ : ∃ r ∈ Set.Ioo (-2 : ℝ) (-1), r ^ 3 - 2 * r ^ 2 - 2 * r + 2 = 0 :=
    intermediate_value_Ioo (by norm_num) hf.continuousOn ⟨by norm_num, by norm_num⟩
  obtain ⟨b, ⟨hb1, hb2⟩, hb⟩ : ∃ r ∈ Set.Ioo (0 : ℝ) 1, r ^ 3 - 2 * r ^ 2 - 2 * r + 2 = 0 :=
    intermediate_value_Ioo' (by norm_num) hf.continuousOn ⟨by norm_num, by norm_num⟩
  obtain ⟨c, ⟨hc1, hc2⟩, hc⟩ : ∃ r ∈ Set.Ioo (2 : ℝ) 3, r ^ 3 - 2 * r ^ 2 - 2 * r + 2 = 0 :=
    intermediate_value_Ioo (by norm_num) hf.continuousOn ⟨by norm_num, by norm_num⟩
  have hp : Matrix.charpoly (HouseGraph.adjMatrix ℝ) ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hroot : ∀ r : ℝ, r * (r + 2) * (r ^ 3 - 2 * r ^ 2 - 2 * r + 2) = 0 →
      r ∈ (Matrix.charpoly (HouseGraph.adjMatrix ℝ)).roots := by
    intro r hr
    rw [mem_roots hp, IsRoot.def, house_charpoly_wow]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
    linear_combination hr
  have hnd : (0 ::ₘ -2 ::ₘ a ::ₘ b ::ₘ c ::ₘ 0 : Multiset ℝ).Nodup := by
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.notMem_zero, or_false,
      Multiset.nodup_zero, and_true]
    simp only [not_or]
    repeat' constructor
    all_goals intro h; first | exact h | linarith
  have hle : (0 ::ₘ -2 ::ₘ a ::ₘ b ::ₘ c ::ₘ 0 : Multiset ℝ) ≤
      (Matrix.charpoly (HouseGraph.adjMatrix ℝ)).roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> apply hroot
    · ring
    · ring
    · rw [ha, mul_zero]
    · rw [hb, mul_zero]
    · rw [hc, mul_zero]
  have hroots : (Matrix.charpoly (HouseGraph.adjMatrix ℝ)).roots =
      0 ::ₘ -2 ::ₘ a ::ₘ b ::ₘ c ::ₘ 0 := by
    symm
    apply Multiset.eq_of_le_of_card_le hle
    calc Multiset.card (Matrix.charpoly (HouseGraph.adjMatrix ℝ)).roots
        ≤ (Matrix.charpoly (HouseGraph.adjMatrix ℝ)).natDegree := card_roots' _
      _ = 5 := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
      _ = _ := by simp
  have h1 : ¬ (0 : ℝ) < a := by linarith
  have h2 : (0 : ℝ) > a := by linarith
  have h3 : (0 : ℝ) ≠ a := by intro h; linarith
  have h4 : ¬ (0 : ℝ) > b := by linarith
  have h5 : (0 : ℝ) ≠ b := by intro h; linarith
  have h6 : ¬ (0 : ℝ) > c := by linarith
  have h7 : (0 : ℝ) ≠ c := by intro h; linarith
  have h8 : (0 : ℝ) < c := by linarith
  unfold cvetkovic
  rw [hroots]
  simp only [Multiset.countP_cons, Multiset.countP_zero, h1, h2, h3, h4, h5, h6, h7, h8, hb1,
    if_true, if_false]
  norm_num

end OpenProofs.WrittenOnTheWallII.Test
