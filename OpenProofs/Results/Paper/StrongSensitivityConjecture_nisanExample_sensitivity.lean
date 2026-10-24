import FormalConjectures.Paper.StrongSensitivityConjecture

/-!
# `StrongSensitivityConjecture.nisanExample_sensitivity`

Upstream: `StrongSensitivityConjecture.nisanExample_sensitivity` (category test), `FormalConjectures/Paper/StrongSensitivityConjecture.lean` line 135.
Proof idea: write `n = 4k` and `W` for the Hamming weight of `x`. Then `nisanExample` accepts
exactly when `W = 2k` or `W = 2k + 1`, and flipping bit `i` changes the weight to `W - 1` (if
`x i`) or `W + 1` (otherwise). Hence the local sensitivity is
`(if [W - 1 accepted] = [W accepted] then 0 else W) + (if [W + 1 accepted] = [W accepted] then 0 else 4k - W)`,
which a case split bounds by `2k + 2`; the input with `x i ↔ i < 2k + 2` attains it.
-/

open Finset Function
open StrongSensitivityConjecture

namespace OpenProofs.StrongSensitivityConjecture

variable {n : ℕ}

theorem nisanSens_card_flip (x : Fin n → Bool) (i : Fin n) :
    #{j | StrongSensitivityConjecture.flip x {i} j} = if x i then #{j | x j} - 1 else #{j | x j} + 1 := by
  by_cases hx : x i = true
  · have h : ({j | StrongSensitivityConjecture.flip x {i} j} : Finset (Fin n)) = ({j | x j} : Finset (Fin n)).erase i := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [StrongSensitivityConjecture.flip, hx]
      · simp [StrongSensitivityConjecture.flip, hj]
    rw [h, card_erase_of_mem (by simp [hx]), if_pos hx]
  · have h : ({j | StrongSensitivityConjecture.flip x {i} j} : Finset (Fin n)) = insert i ({j | x j} : Finset (Fin n)) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [StrongSensitivityConjecture.flip, hx]
      · simp [StrongSensitivityConjecture.flip, hj]
    rw [h, card_insert_of_notMem (by simp [hx]), if_neg hx]

theorem nisanSens_value (k : ℕ) (x : Fin (4 * k) → Bool) :
    nisanExample (4 * k) x = decide (#{i | x i} = 2 * k ∨ #{i | x i} = 2 * k + 1) := by
  unfold nisanExample
  simp only [Finset.mem_insert, Finset.mem_singleton, decide_eq_decide]
  have e : ((4 * k : ℕ) : ℚ) / 2 = ((2 * k : ℕ) : ℚ) := by push_cast; ring
  rw [e]
  norm_cast

theorem nisanSens_at (k : ℕ) (x : Fin (4 * k) → Bool) :
    sensitivityAt (nisanExample (4 * k)) x =
      (if ((#{i | x i} - 1 = 2 * k ∨ #{i | x i} - 1 = 2 * k + 1) ↔
          (#{i | x i} = 2 * k ∨ #{i | x i} = 2 * k + 1)) then 0 else #{i | x i}) +
      (if ((#{i | x i} + 1 = 2 * k ∨ #{i | x i} + 1 = 2 * k + 1) ↔
          (#{i | x i} = 2 * k ∨ #{i | x i} = 2 * k + 1)) then 0 else 4 * k - #{i | x i}) := by
  have htot : #{i | x i} + #{i | ¬ x i = true} = 4 * k := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  unfold sensitivityAt
  rw [← card_filter_add_card_filter_not (s := ({i | nisanExample (4 * k) (flip x {i}) ≠
    nisanExample (4 * k) x} : Finset (Fin (4 * k)))) (fun i => x i = true), filter_filter,
    filter_filter]
  congr 1
  · split_ifs with h
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro i - ⟨hs, hx⟩
      apply hs
      rw [nisanSens_value, nisanSens_value, nisanSens_card_flip, if_pos hx, decide_eq_decide]
      exact h
    · congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro hx
      rw [nisanSens_value, nisanSens_value, nisanSens_card_flip, if_pos hx, Ne, decide_eq_decide]
      exact h
  · split_ifs with h
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro i - ⟨hs, hx⟩
      apply hs
      rw [nisanSens_value, nisanSens_value, nisanSens_card_flip, if_neg hx, decide_eq_decide]
      exact h
    · rw [show 4 * k - #{i | x i} = #{i | ¬ x i = true} by omega]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro hx
      rw [nisanSens_value, nisanSens_value, nisanSens_card_flip, if_neg hx, Ne, decide_eq_decide]
      exact h

theorem nisanSens_card_le (x : Fin n → Bool) : #{i | x i} ≤ n := by
  calc #{i | x i} ≤ #(univ : Finset (Fin n)) := card_filter_le _ _
    _ = n := by rw [card_univ, Fintype.card_fin]

theorem nisanExample_sensitivity (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    sensitivity (nisanExample n) = n / 2 + 2 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : 1 ≤ k := by omega
  have h2 : 4 * k / 2 = 2 * k := by omega
  rw [h2]
  unfold sensitivity
  apply le_antisymm
  · apply Finset.sup_le
    intro x _
    rw [nisanSens_at]
    have hW := nisanSens_card_le x
    split_ifs <;> omega
  · let x₀ : Fin (4 * k) → Bool := fun i => decide ((i : ℕ) < 2 * k + 2)
    have hW : #{i | x₀ i} = 2 * k + 2 := by
      have : ({i | x₀ i} : Finset (Fin (4 * k))) = ({i | (i : ℕ) < 2 * k + 2} : Finset (Fin (4 * k))) := by
        ext i; simp [x₀]
      rw [this, Fin.card_filter_val_lt]
      omega
    calc 2 * k + 2 = sensitivityAt (nisanExample (4 * k)) x₀ := by
          rw [nisanSens_at, hW]
          split_ifs <;> omega
      _ ≤ univ.sup (sensitivityAt (nisanExample (4 * k))) := le_sup (mem_univ x₀)

end OpenProofs.StrongSensitivityConjecture
