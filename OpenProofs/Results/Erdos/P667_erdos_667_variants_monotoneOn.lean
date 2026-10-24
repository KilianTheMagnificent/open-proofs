import FormalConjectures.ErdosProblems.«667»

/-!
# `Erdos667.erdos_667.variants.monotoneOn`

Upstream: `Erdos667.erdos_667.variants.monotoneOn` (category textbook), `FormalConjectures/ErdosProblems/667.lean` line 89.
Proof idea: for `q₁ ≤ q₂` every `(p, q₂)`-locally dense graph is `(p, q₁)`-locally dense, so the
predicate defining `H p q₁ n` implies the one defining `H p q₂ n` and `Nat.findGreatest_mono_left`
gives `H p q₁ n ≤ H p q₂ n`. Hence `log (H p q₁ n) / log n ≤ log (H p q₂ n) / log n` for every `n`
(`log` of a natural is nonnegative, `log 0 = 0`). The first sequence is bounded below by `0` and
the second is bounded above by `1` (since `H p q n ≤ n`), so `Filter.liminf_le_liminf` applies in `ℝ`.
-/

open SimpleGraph Filter
open Erdos667

namespace OpenProofs.Erdos667

theorem H_mono_q_op667 (p : ℕ) {q₁ q₂ : ℕ} (h : q₁ ≤ q₂) (n : ℕ) : H p q₁ n ≤ H p q₂ n := by
  classical
  unfold H
  apply Nat.findGreatest_mono_left
  intro m hm G hG
  exact hm G (fun s hs => le_trans h (hG s hs))

theorem ratio_nonneg_op667 (p q n : ℕ) : 0 ≤ Real.log (H p q n) / Real.log n :=
  div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem ratio_le_one_op667 (p q n : ℕ) : Real.log (H p q n) / Real.log n ≤ 1 := by
  apply div_le_one_of_le₀ _ (Real.log_natCast_nonneg _)
  have hle : H p q n ≤ n := by
    classical
    unfold H
    exact Nat.findGreatest_le n
  rcases Nat.eq_zero_or_pos (H p q n) with h0 | hpos
  · rw [h0]
    simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)

theorem erdos_667.variants.monotoneOn (p : ℕ) :
    MonotoneOn (c p) (Set.Icc 1 (Nat.choose (p - 1) 2 + 1)) := by
  intro q₁ _ q₂ _ h
  unfold c
  apply Filter.liminf_le_liminf
  · refine Filter.Eventually.of_forall (fun n => ?_)
    apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg _)
    have hle := H_mono_q_op667 p h n
    rcases Nat.eq_zero_or_pos (H p q₁ n) with h0 | hpos
    · rw [h0]
      simpa using Real.log_natCast_nonneg (H p q₂ n)
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  · exact Filter.isBoundedUnder_of ⟨0, fun n => ratio_nonneg_op667 p q₁ n⟩
  · exact (Filter.isBoundedUnder_of ⟨1, fun n => ratio_le_one_op667 p q₂ n⟩).isCoboundedUnder_flip

end OpenProofs.Erdos667
