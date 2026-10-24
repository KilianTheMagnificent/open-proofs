import FormalConjectures.WrittenOnTheWallII.Test

/-!
# `WrittenOnTheWallII.Test.Star5_cvetkovic`

Upstream: `WrittenOnTheWallII.Test.Star5_cvetkovic` (category test), `FormalConjectures/WrittenOnTheWallII/Test.lean` line 632.
Proof idea: reindex the adjacency matrix of `K_{1,5}` along `Fin 1 ⊕ Fin 5 ≃ Fin 6`
(`Matrix.charpoly_reindex`), write its characteristic matrix explicitly and expand the
determinant along the first row to get `charpoly = X^6 - 5 X^4 = X^4 (X - √5)(X + √5)`. The root
multiset is `{0, 0, 0, 0, √5, -√5}`: four zero eigenvalues, one positive and one negative, so
`4 + min 1 1 = 5`.
-/

open SimpleGraph Polynomial
open WrittenOnTheWallII.Test

namespace OpenProofs.WrittenOnTheWallII.Test

theorem star5_charmatrix_wow :
    Matrix.charmatrix (Matrix.reindex finSumFinEquiv finSumFinEquiv (Star5.adjMatrix ℝ)) =
    !![X, -1, -1, -1, -1, -1;
       -1, X, 0, 0, 0, 0;
       -1, 0, X, 0, 0, 0;
       -1, 0, 0, X, 0, 0;
       -1, 0, 0, 0, X, 0;
       -1, 0, 0, 0, 0, X] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp +decide [adjMatrix_apply]

theorem star5_charpoly_wow : Matrix.charpoly (Star5.adjMatrix ℝ) = X ^ 6 - 5 * X ^ 4 := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv, Matrix.charpoly, star5_charmatrix_wow]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem star5_charpoly_factor_wow : (X ^ 6 - 5 * X ^ 4 : ℝ[X]) =
    (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C √5) * (X - C (-√5)) := by
  have h : (C √5 : ℝ[X]) * C √5 = 5 := by
    rw [← C_mul, Real.mul_self_sqrt (by norm_num)]; rfl
  simp only [C_0, sub_zero, C_neg, sub_neg_eq_add]
  linear_combination (X ^ 4) * h

theorem Star5_cvetkovic : cvetkovic Star5 = 5 := by
  have hne : ∀ a : ℝ, (X - C a : ℝ[X]) ≠ 0 := fun a => X_sub_C_ne_zero a
  have hroots : (Matrix.charpoly (Star5.adjMatrix ℝ)).roots =
      0 ::ₘ 0 ::ₘ 0 ::ₘ 0 ::ₘ √5 ::ₘ -√5 ::ₘ 0 := by
    rw [star5_charpoly_wow, star5_charpoly_factor_wow]
    simp only [roots_mul, mul_ne_zero_iff, hne, ne_eq, not_false_eq_true, and_self,
      roots_X_sub_C]
    rfl
  have hs : (0 : ℝ) < √5 := by positivity
  unfold cvetkovic
  rw [hroots]
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  simp [hs, hs.ne, hs.ne', not_lt.mpr hs.le]

end OpenProofs.WrittenOnTheWallII.Test
