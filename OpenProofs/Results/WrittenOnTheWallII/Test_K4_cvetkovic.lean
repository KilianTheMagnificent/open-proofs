import FormalConjectures.WrittenOnTheWallII.Test

/-!
# `WrittenOnTheWallII.Test.K4_cvetkovic`

Upstream: `WrittenOnTheWallII.Test.K4_cvetkovic` (category test), `FormalConjectures/WrittenOnTheWallII/Test.lean` line 290.
Proof idea: write the characteristic matrix of the adjacency matrix of `K4` explicitly, expand
the determinant along the first row to get `charpoly = (X - 3)(X + 1)^3`, read off the root
multiset `{3, -1, -1, -1}`, and count: no zero eigenvalue, one positive and three negative,
so `0 + min 1 3 = 1`.
-/

open SimpleGraph Polynomial
open WrittenOnTheWallII.Test

namespace OpenProofs.WrittenOnTheWallII.Test

theorem k4_charmatrix_wow : Matrix.charmatrix (K4.adjMatrix ℝ) =
    !![X, -1, -1, -1;
       -1, X, -1, -1;
       -1, -1, X, -1;
       -1, -1, -1, X] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp +decide

theorem k4_charpoly_wow : Matrix.charpoly (K4.adjMatrix ℝ) =
    (X - C 3) * ((X - C (-1)) * (X - C (-1)) * (X - C (-1))) := by
  rw [Matrix.charpoly, k4_charmatrix_wow]
  have h3 : (C 3 : ℝ[X]) = 3 := C_ofNat 3
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, h3]
  ring

theorem K4_cvetkovic : cvetkovic K4 = 1 := by
  have hne : ∀ a : ℝ, (X - C a : ℝ[X]) ≠ 0 := fun a => X_sub_C_ne_zero a
  have hroots : (Matrix.charpoly (K4.adjMatrix ℝ)).roots =
      3 ::ₘ (-1) ::ₘ (-1) ::ₘ (-1) ::ₘ 0 := by
    rw [k4_charpoly_wow]
    simp only [roots_mul, mul_ne_zero_iff, hne, ne_eq, not_false_eq_true, and_self,
      roots_X_sub_C]
    rfl
  unfold cvetkovic
  rw [hroots]
  simp only [Multiset.countP_cons, Multiset.countP_zero]
  norm_num

end OpenProofs.WrittenOnTheWallII.Test
