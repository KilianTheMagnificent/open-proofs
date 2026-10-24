import FormalConjectures.OEIS.«87719»

/-!
# `OeisA87719.a_exists`

Upstream: `OeisA87719.a_exists` (category textbook), `FormalConjectures/OEIS/87719.lean` line 49.
Proof idea: the two counts partition `Icc 1 m`, so it suffices that `2 * countExceeding n m > m`.
Put `N = 3 ^ n`. Every `k > N` divisible by `2` or `3` has `minFac k ≤ 3`, hence
`minFac k ^ n ≤ N < k`. So in each block `6j+1, …, 6j+6` with `N ≤ 6j` at least four numbers
(`6j+2, 6j+3, 6j+4, 6j+6`) are exceeding. By induction `countExceeding n (6 (N + t)) ≥ 4 t`;
taking `t = 3N + 1` gives `countExceeding ≥ 12N + 4 > (24N + 6) / 2`.
-/

open Nat
open OeisA87719

namespace OpenProofs.OeisA87719

theorem a87719_countExceeding_succ (n m : ℕ) :
    countExceeding n (m + 1) =
      countExceeding n m + if (m + 1).minFac ^ n < m + 1 then 1 else 0 := by
  unfold countExceeding
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ m + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

theorem a87719_count_sum (n m : ℕ) : countExceeding n m + countNotExceeding n m = m := by
  unfold countExceeding countNotExceeding
  have := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 m)
    (fun k => k > k.minFac ^ n)
  simp only [not_lt] at this
  rw [this, Nat.card_Icc]
  omega

theorem a_exists (n : ℕ) : ∃ m, countExceeding n m > countNotExceeding n m := by
  have key : ∀ k, 3 ^ n < k → (2 ∣ k ∨ 3 ∣ k) → k.minFac ^ n < k := by
    intro k hk hd
    have h3 : k.minFac ≤ 3 := by
      rcases hd with hd | hd
      · have := Nat.minFac_le_of_dvd (le_refl 2) hd
        omega
      · exact Nat.minFac_le_of_dvd (by norm_num) hd
    exact lt_of_le_of_lt (Nat.pow_le_pow_left h3 n) hk
  have hstep : ∀ j, 3 ^ n ≤ 6 * j →
      countExceeding n (6 * j) + 4 ≤ countExceeding n (6 * (j + 1)) := by
    intro j hj
    have e : 6 * (j + 1) = 6 * j + 1 + 1 + 1 + 1 + 1 + 1 := by ring
    rw [e, a87719_countExceeding_succ, a87719_countExceeding_succ, a87719_countExceeding_succ,
      a87719_countExceeding_succ, a87719_countExceeding_succ, a87719_countExceeding_succ]
    have h2 := key (6 * j + 1 + 1) (by omega) (Or.inl ⟨3 * j + 1, by ring⟩)
    have h3 := key (6 * j + 1 + 1 + 1) (by omega) (Or.inr ⟨2 * j + 1, by ring⟩)
    have h4 := key (6 * j + 1 + 1 + 1 + 1) (by omega) (Or.inl ⟨3 * j + 2, by ring⟩)
    have h6 := key (6 * j + 1 + 1 + 1 + 1 + 1 + 1) (by omega) (Or.inl ⟨3 * j + 3, by ring⟩)
    rw [if_pos h2, if_pos h3, if_pos h4, if_pos h6]
    split_ifs <;> omega
  have hind : ∀ t, 4 * t ≤ countExceeding n (6 * (3 ^ n + t)) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := hstep (3 ^ n + t) (by omega)
      rw [show 3 ^ n + (t + 1) = 3 ^ n + t + 1 by ring]
      omega
  refine ⟨6 * (3 ^ n + (3 * 3 ^ n + 1)), ?_⟩
  have h1 := hind (3 * 3 ^ n + 1)
  have h2 := a87719_count_sum n (6 * (3 ^ n + (3 * 3 ^ n + 1)))
  omega

end OpenProofs.OeisA87719
