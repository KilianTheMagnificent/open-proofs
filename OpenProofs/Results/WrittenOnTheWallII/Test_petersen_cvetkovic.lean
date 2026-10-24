import FormalConjectures.WrittenOnTheWallII.Test

/-!
# `WrittenOnTheWallII.Test.petersen_cvetkovic`

Upstream: `WrittenOnTheWallII.Test.petersen_cvetkovic` (category test), `FormalConjectures/WrittenOnTheWallII/Test.lean` line 398.
Proof idea: diagonalize the adjacency matrix with an explicit integer eigenvector matrix `P`
(one eigenvector for `3`, five for `1`, four for `-2`). Over `ℤ`, kernel `decide` checks
`A * P = P * diagonal d` and `Q * P = 30 • 1` for an explicit integer `Q`. Mapping to `ℝ`,
`P` has inverse `30⁻¹ • Q`, so `charpoly_mul_comm` gives `charpoly A = charpoly (diagonal d)
= ∏ (X - C dᵢ)`, whose root multiset is `{3, 1, 1, 1, 1, 1, -2, -2, -2, -2}`: no zero
eigenvalue, six positive and four negative ones, so `cvetkovic = 0 + min 6 4 = 4`.
-/

open SimpleGraph Polynomial
open WrittenOnTheWallII.Test

namespace OpenProofs.WrittenOnTheWallII.Test

/-- Integer eigenvector matrix of the Petersen graph (columns: one eigenvector for `3`,
five for `1`, four for `-2`). -/
def petersenEigP : Matrix (Fin 10) (Fin 10) ℤ :=
  !![1, 1, 0, -1, -1, 0, 2, 1, 1, 2;
     1, 0, 1, 0, -1, -1, -2, 0, -1, -1;
     1, -1, 0, 1, 0, -1, 1, -1, 1, 0;
     1, -1, -1, 0, 1, 0, 0, 1, -1, 1;
     1, 0, -1, -1, 0, 1, -1, -1, 0, -2;
     1, 1, 0, 0, 0, 0, -1, -1, -1, -1;
     1, 0, 1, 0, 0, 0, 1, 0, 0, 0;
     1, 0, 0, 1, 0, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 1, 0, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 1, 0, 0, 0, 1]

/-- `30` times the inverse of `petersenEigP`. -/
def petersenEigQ : Matrix (Fin 10) (Fin 10) ℤ :=
  !![3, 3, 3, 3, 3, 3, 3, 3, 3, 3;
     5, -5, -5, -5, -5, 15, -5, 5, 5, -5;
     -5, 5, -5, -5, -5, -5, 15, -5, 5, 5;
     -5, -5, 5, -5, -5, 5, -5, 15, -5, 5;
     -5, -5, -5, 5, -5, 5, 5, -5, 15, -5;
     -5, -5, -5, -5, 5, -5, 5, 5, -5, 15;
     2, -8, 2, 2, 2, 2, 12, 2, -8, -8;
     2, 2, -8, 2, 2, -8, 2, 12, 2, -8;
     2, 2, 2, -8, 2, -8, -8, 2, 12, 2;
     2, 2, 2, 2, -8, 2, -8, -8, 2, 12]

/-- The eigenvalues, in the order of the columns of `petersenEigP`. -/
def petersenEigD : Fin 10 → ℤ := ![3, 1, 1, 1, 1, 1, -2, -2, -2, -2]

theorem petersen_adj_mul_eigP_wow :
    PetersenGraph.adjMatrix ℤ * petersenEigP = petersenEigP * Matrix.diagonal petersenEigD := by
  decide +kernel

theorem petersen_eigQ_mul_eigP_wow :
    petersenEigQ * petersenEigP = (30 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  decide +kernel

theorem petersen_adjMatrix_real_wow :
    PetersenGraph.adjMatrix ℝ = (PetersenGraph.adjMatrix ℤ).map (Int.castRingHom ℝ) := by
  ext i j
  simp [adjMatrix_apply]

theorem petersen_charpoly_wow : Matrix.charpoly (PetersenGraph.adjMatrix ℝ) =
    ∏ i, (X - C ((petersenEigD i : ℤ) : ℝ)) := by
  have hAP : PetersenGraph.adjMatrix ℝ * petersenEigP.map (Int.castRingHom ℝ) =
      petersenEigP.map (Int.castRingHom ℝ) *
        (Matrix.diagonal petersenEigD).map (Int.castRingHom ℝ) := by
    rw [petersen_adjMatrix_real_wow, ← Matrix.map_mul, ← Matrix.map_mul,
      petersen_adj_mul_eigP_wow]
  have hQP : ((30⁻¹ : ℝ) • petersenEigQ.map (Int.castRingHom ℝ)) *
      petersenEigP.map (Int.castRingHom ℝ) = 1 := by
    rw [Matrix.smul_mul, ← Matrix.map_mul, petersen_eigQ_mul_eigP_wow]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  have hPQ := mul_eq_one_comm.mp hQP
  have hD : (Matrix.diagonal petersenEigD).map (Int.castRingHom ℝ) =
      Matrix.diagonal fun i => ((petersenEigD i : ℤ) : ℝ) := by
    simp [Matrix.diagonal_map]
  calc (PetersenGraph.adjMatrix ℝ).charpoly
      = (PetersenGraph.adjMatrix ℝ * (petersenEigP.map (Int.castRingHom ℝ) *
          ((30⁻¹ : ℝ) • petersenEigQ.map (Int.castRingHom ℝ)))).charpoly := by
        rw [hPQ, Matrix.mul_one]
    _ = (((30⁻¹ : ℝ) • petersenEigQ.map (Int.castRingHom ℝ)) *
          (PetersenGraph.adjMatrix ℝ * petersenEigP.map (Int.castRingHom ℝ))).charpoly := by
        rw [← Matrix.mul_assoc, Matrix.charpoly_mul_comm]
    _ = ((Matrix.diagonal petersenEigD).map (Int.castRingHom ℝ)).charpoly := by
        rw [hAP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
    _ = _ := by rw [hD, Matrix.charpoly_diagonal]

theorem petersen_cvetkovic : cvetkovic PetersenGraph = 4 := by
  have hroots : (Matrix.charpoly (PetersenGraph.adjMatrix ℝ)).roots =
      Multiset.map (fun i => ((petersenEigD i : ℤ) : ℝ)) Finset.univ.val := by
    have hmap : Multiset.map (fun i => (X - C ((petersenEigD i : ℤ) : ℝ) : ℝ[X]))
        Finset.univ.val = (Multiset.map (fun i => ((petersenEigD i : ℤ) : ℝ))
        Finset.univ.val).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [petersen_charpoly_wow, Finset.prod_eq_multiset_prod, hmap,
      Polynomial.roots_multiset_prod_X_sub_C]
  unfold cvetkovic
  rw [hroots, Fin.univ_val_map]
  simp [List.ofFn_succ, petersenEigD]

end OpenProofs.WrittenOnTheWallII.Test
