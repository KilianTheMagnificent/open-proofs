import FormalConjectures.WrittenOnTheWallII.Test

/-!
# `WrittenOnTheWallII.Test.C6_cvetkovic`

Upstream: `WrittenOnTheWallII.Test.C6_cvetkovic` (category test), `FormalConjectures/WrittenOnTheWallII/Test.lean` line 497.
Proof idea: the characteristic matrix of the adjacency matrix of `cycleGraph 6` is written out
entrywise, and Laplace expansion along the first row (`Matrix.det_succ_row_zero`) gives the
characteristic polynomial `(X - 2)(X + 2)(X - 1)²(X + 1)²`. Its root multiset is
`{2, -2, 1, 1, -1, -1}`: no zero eigenvalue, three positive and three negative ones, so
`cvetkovic C6 = 0 + min 3 3 = 3`.
-/

open SimpleGraph Polynomial
open WrittenOnTheWallII.Test

namespace OpenProofs.WrittenOnTheWallII.Test

theorem c6_charmatrix_wow : Matrix.charmatrix (C6.adjMatrix ℝ) =
    !![X, -1, 0, 0, 0, -1;
       -1, X, -1, 0, 0, 0;
       0, -1, X, -1, 0, 0;
       0, 0, -1, X, -1, 0;
       0, 0, 0, -1, X, -1;
       -1, 0, 0, 0, -1, X] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp +decide [adjMatrix_apply]

theorem c6_charpoly_wow : Matrix.charpoly (C6.adjMatrix ℝ) =
    (X - C 2) * (X - C (-2)) * ((X - C 1) * (X - C 1)) * ((X - C (-1)) * (X - C (-1))) := by
  rw [Matrix.charpoly, c6_charmatrix_wow]
  have h2 : (C 2 : ℝ[X]) = 2 := map_ofNat C 2
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, h2]
  ring

theorem C6_cvetkovic : cvetkovic C6 = 3 := by
  have hne : ∀ a : ℝ, (X - C a : ℝ[X]) ≠ 0 := fun a => X_sub_C_ne_zero a
  have hroots : (Matrix.charpoly (C6.adjMatrix ℝ)).roots =
      2 ::ₘ -2 ::ₘ 1 ::ₘ 1 ::ₘ -1 ::ₘ -1 ::ₘ 0 := by
    rw [c6_charpoly_wow]
    simp only [roots_mul, mul_ne_zero_iff, hne, ne_eq, not_false_eq_true, and_self,
      roots_X_sub_C]
    rfl
  unfold cvetkovic
  rw [hroots]
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  norm_num

end OpenProofs.WrittenOnTheWallII.Test
