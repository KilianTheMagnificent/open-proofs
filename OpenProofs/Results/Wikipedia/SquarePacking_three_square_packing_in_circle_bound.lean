import FormalConjectures.Wikipedia.SquarePacking

/-!
# `SquarePacking.three_square_packing_in_circle_bound`

Upstream: `SquarePacking.three_square_packing_in_circle_bound` (category textbook), `FormalConjectures/Wikipedia/SquarePacking.lean` line 155.
Proof idea: translate the open unit square by (-1, -13/16), (0, -13/16) and (-1/2, 3/16):
two squares side by side with the third centred on top. The bottom pair has |x| < 1,
|y| < 13/16 and the top square |x| < 1/2, |y| < 19/16, so x^2 + y^2 < 425/256 = r^2 with
r = 5 sqrt 17 / 16. Disjointness: the bottom squares are split by x = 0, the top one by y = 3/16.
-/

open EuclideanGeometry
open scoped NNReal
open SquarePacking

namespace OpenProofs.SquarePacking

theorem three_square_packing_in_circle_bound :
    Nonempty (Packing 3 UnitSquare (Circle ((5 * NNReal.sqrt 17) / 16))) := by
  let v : Fin 3 → ℝ² := ![!₂[-1, -13/16], !₂[0, -13/16], !₂[-1/2, 3/16]]
  refine ⟨⟨fun i => IsometryEquiv.vaddConst (v i), ?_, ?_⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro q ⟨p, ⟨hp0, hp1, hp2, hp3⟩, rfl⟩ ⟨p', ⟨hp0', hp1', hp2', hp3'⟩, hq⟩
    have h0 := congrArg (· 0) hq
    have h1 := congrArg (· 1) hq
    simp at h0 h1
    fin_cases i <;> fin_cases j <;> simp [v] at h0 h1 hij <;> linarith
  · intro i
    rintro q ⟨p, ⟨hp0, hp1, hp2, hp3⟩, rfl⟩
    show (_ : ℝ) < _
    have hr : (((5 * NNReal.sqrt 17) / 16 : ℝ≥0) : ℝ) ^ 2 = 425 / 256 := by
      push_cast
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [hr]
    fin_cases i <;> simp [v] <;> nlinarith

end OpenProofs.SquarePacking
