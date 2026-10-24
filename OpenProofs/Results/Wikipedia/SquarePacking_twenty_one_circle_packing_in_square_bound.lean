import FormalConjectures.Wikipedia.SquarePacking

/-!
# `SquarePacking.twenty_one_circle_packing_in_square_bound`

Upstream: `SquarePacking.twenty_one_circle_packing_in_square_bound` (category textbook), `FormalConjectures/Wikipedia/SquarePacking.lean` line 187.
Proof idea: translate the open unit disc to 21 centres `(a i / 10⁴, b i / 10⁴)` with integer
`10⁴ ≤ a i, b i ≤ 83590`, i.e. every centre lies in `[1, 8.359]²`, so each disc lies in the open
square `(0, 9.359)²`. The centres come from a numerically optimized 21-point spread in the square
(minimum distance ≈ 0.2718122 in the unit square, side ≈ 9.35802 for unit discs), scaled and
rounded; pairwise squared distances are at least `4 · 10⁸` (checked by `decide`). Two discs whose
centres are at distance at least 2 are disjoint since `|p' - p|² ≤ 2|p|² + 2|p'|² < 4`.
-/

open EuclideanGeometry
open scoped NNReal
open SquarePacking

namespace OpenProofs.SquarePacking

/-- Unit discs centred at points of `[1, s - 1]²` with pairwise distance at least `2` form a
packing in the open square of side `s`. -/
theorem op_sq21_packing_of_centers {n : ℕ} (s : ℝ) (c : Fin n → ℝ²)
    (hb : ∀ i, 1 ≤ c i 0 ∧ c i 0 ≤ s - 1 ∧ 1 ≤ c i 1 ∧ c i 1 ≤ s - 1)
    (hd : ∀ i j, i ≠ j → 4 ≤ (c i 0 - c j 0) ^ 2 + (c i 1 - c j 1) ^ 2) :
    Nonempty (Packing n UnitCircle (Square s)) := by
  refine ⟨⟨fun i => IsometryEquiv.vaddConst (c i), ?_, ?_⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro q ⟨p, hp, rfl⟩ ⟨p', hp', hq⟩
    have h0 := congrArg (· 0) hq
    have h1 := congrArg (· 1) hq
    simp at h0 h1
    simp only [UnitCircle, SquarePacking.Circle, Set.mem_ofPred_eq, NNReal.coe_one, one_pow] at hp hp'
    have e0 : c i 0 - c j 0 = p' 0 - p 0 := by linarith
    have e1 : c i 1 - c j 1 = p' 1 - p 1 := by linarith
    have := hd i j hij
    rw [e0, e1] at this
    nlinarith [sq_nonneg (p 0 + p' 0), sq_nonneg (p 1 + p' 1)]
  · intro i
    rintro q ⟨p, hp, rfl⟩
    simp only [UnitCircle, SquarePacking.Circle, Set.mem_ofPred_eq, NNReal.coe_one, one_pow] at hp
    obtain ⟨h1, h2, h3, h4⟩ := hb i
    have a0 : p 0 < 1 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 0 - 1)]
    have b0 : -1 < p 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 0 + 1)]
    have a1 : p 1 < 1 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1 - 1)]
    have b1 : -1 < p 1 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1 + 1)]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith

/-- First coordinates of the centres, times `10⁴`. -/
def op_sq21_a : Fin 21 → ℕ :=
  ![10000, 23510, 26864, 29545, 43512, 53589, 43729, 83588, 73663, 83588, 43656, 53509, 33507,
    12671, 63658, 75096, 63586, 10000, 10000, 83588, 63658]

/-- Second coordinates of the centres, times `10⁴`. -/
def op_sq21_b : Fin 21 → ℕ :=
  ![83588, 27324, 72833, 47684, 27324, 44603, 83588, 83588, 10000, 27366, 61965, 10000, 10000,
    10067, 81887, 45476, 27278, 62077, 42075, 63586, 61885]

theorem op_sq21_bounds :
    ∀ i, 10000 ≤ op_sq21_a i ∧ op_sq21_a i ≤ 83590 ∧ 10000 ≤ op_sq21_b i ∧
      op_sq21_b i ≤ 83590 := by
  decide

theorem op_sq21_dist :
    ∀ i j : Fin 21, i ≠ j → (400000000 : ℤ) ≤
      ((op_sq21_a i : ℤ) - op_sq21_a j) ^ 2 + ((op_sq21_b i : ℤ) - op_sq21_b j) ^ 2 := by
  decide

theorem twenty_one_circle_packing_in_square_bound :
    Nonempty (Packing 21 UnitCircle (Square 9.359)) := by
  refine op_sq21_packing_of_centers 9.359
    (fun i => !₂[(op_sq21_a i : ℝ) / 10000, (op_sq21_b i : ℝ) / 10000]) ?_ ?_
  · intro i
    obtain ⟨h1, h2, h3, h4⟩ := op_sq21_bounds i
    have h1' : (10000 : ℝ) ≤ op_sq21_a i := by exact_mod_cast h1
    have h2' : (op_sq21_a i : ℝ) ≤ 83590 := by exact_mod_cast h2
    have h3' : (10000 : ℝ) ≤ op_sq21_b i := by exact_mod_cast h3
    have h4' : (op_sq21_b i : ℝ) ≤ 83590 := by exact_mod_cast h4
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [div_le_iff₀ (by norm_num)]; linarith
    · rw [le_div_iff₀ (by norm_num)]; linarith
    · rw [div_le_iff₀ (by norm_num)]; linarith
  · intro i j hij
    have h := op_sq21_dist i j hij
    have h' : (400000000 : ℝ) ≤
        ((op_sq21_a i : ℝ) - op_sq21_a j) ^ 2 + ((op_sq21_b i : ℝ) - op_sq21_b j) ^ 2 := by
      exact_mod_cast h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e : ((op_sq21_a i : ℝ) / 10000 - (op_sq21_a j : ℝ) / 10000) ^ 2 +
        ((op_sq21_b i : ℝ) / 10000 - (op_sq21_b j : ℝ) / 10000) ^ 2 =
        (((op_sq21_a i : ℝ) - op_sq21_a j) ^ 2 + ((op_sq21_b i : ℝ) - op_sq21_b j) ^ 2) /
          100000000 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    linarith

end OpenProofs.SquarePacking
