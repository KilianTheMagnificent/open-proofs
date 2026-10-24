import FormalConjectures.Paper.StrongSensitivityConjecture

/-!
# `StrongSensitivityConjecture.nisanExample_blockSensitivity`

Upstream: `StrongSensitivityConjecture.nisanExample_blockSensitivity` (category test), `FormalConjectures/Paper/StrongSensitivityConjecture.lean` line 144.
Proof idea: write `n = 4m` (`m ≥ 2`). For a block `B` with `a` one-bits and `b` zero-bits of `x`,
flipping `B` turns the weight `w` of `x` into `w'` with `w' + a = w + b`; the function accepts
exactly weights `2m` and `2m+1`. Depending on `w`, every sensitive block satisfies
`2 ≤ α a + β b` for a fixed pair `(α, β)` (`(2,1)` at `w = 2m`, `(1,2)` at `w = 2m+1`, `(0,2)` at
`w = 2m-1`, `(0,1)` below, `(2,0)` at `w = 2m+2`, `(1,0)` above), and disjointness gives
`2 · #blocks ≤ α w + β (4m - w) ≤ 6m`. For the lower bound take `x` with ones exactly at the
first `2m` positions, the `2m` one-bits as singleton blocks and `m` pairs of zero-bits.
-/

open Finset Function
open StrongSensitivityConjecture

namespace OpenProofs.StrongSensitivityConjecture

variable {n : ℕ}

theorem nisanBS_flip_weight (x : Fin n → Bool) (B : Finset (Fin n)) :
    #{i | flip x B i = true} + #(B.filter (fun i => x i = true)) =
      #{i | x i = true} + #(B.filter (fun i => x i = false)) := by
  have h1 := card_filter_add_card_filter_not (s := univ.filter (fun i => flip x B i = true))
    (fun i => i ∈ B)
  have h2 := card_filter_add_card_filter_not (s := univ.filter (fun i => x i = true))
    (fun i => i ∈ B)
  have e1 : (univ.filter (fun i => flip x B i = true)).filter (fun i => i ∈ B) =
      B.filter (fun i => x i = false) := by
    ext i; by_cases hi : i ∈ B <;> simp [StrongSensitivityConjecture.flip, hi]
  have e2 : (univ.filter (fun i => flip x B i = true)).filter (fun i => i ∉ B) =
      (univ.filter (fun i => x i = true)).filter (fun i => i ∉ B) := by
    ext i; by_cases hi : i ∈ B <;> simp [StrongSensitivityConjecture.flip, hi]
  have e3 : (univ.filter (fun i => x i = true)).filter (fun i => i ∈ B) =
      B.filter (fun i => x i = true) := by
    ext i; by_cases hi : i ∈ B <;> simp [hi]
  rw [e1, e2] at h1
  rw [e3] at h2
  omega

theorem nisanBS_weight_add (x : Fin n → Bool) :
    #{i | x i = true} + #{i | x i = false} = n := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => x i = true)
  simpa using this

theorem nisanBS_sum_le (cB : Finset (Finset (Fin n)))
    (hd : (cB : Set (Finset (Fin n))).PairwiseDisjoint id) (p : Fin n → Prop) [DecidablePred p] :
    ∑ B ∈ cB, #(B.filter p) ≤ #(univ.filter p) := by
  rw [← card_biUnion]
  · apply card_le_card
    intro i hi
    simp only [mem_biUnion, mem_filter] at hi
    obtain ⟨_, _, _, h⟩ := hi
    simp [h]
  · intro B₁ h₁ B₂ h₂ hne
    exact disjoint_filter_filter (hd h₁ h₂ hne)

theorem nisanBS_card_le (x : Fin n → Bool) (cB : Finset (Finset (Fin n)))
    (hd : (cB : Set (Finset (Fin n))).PairwiseDisjoint id) (α β : ℕ)
    (h : ∀ B ∈ cB, 2 ≤ α * #(B.filter (fun i => x i = true)) +
      β * #(B.filter (fun i => x i = false))) :
    2 * #cB ≤ α * #{i | x i = true} + β * #{i | x i = false} := by
  calc 2 * #cB = ∑ _B ∈ cB, 2 := by simp [mul_comm]
    _ ≤ ∑ B ∈ cB, (α * #(B.filter (fun i => x i = true)) +
          β * #(B.filter (fun i => x i = false))) := sum_le_sum h
    _ = α * ∑ B ∈ cB, #(B.filter (fun i => x i = true)) +
          β * ∑ B ∈ cB, #(B.filter (fun i => x i = false)) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ _ := add_le_add (Nat.mul_le_mul_left _ (nisanBS_sum_le cB hd _))
          (Nat.mul_le_mul_left _ (nisanBS_sum_le cB hd _))

theorem nisanBS_val (m : ℕ) (y : Fin (4 * m) → Bool) :
    nisanExample (4 * m) y =
      decide (#{i | y i = true} = 2 * m ∨ #{i | y i = true} = 2 * m + 1) := by
  have h2 : ((4 * m : ℕ) : ℚ) / 2 = ((2 * m : ℕ) : ℚ) := by push_cast; ring
  simp only [nisanExample, mem_insert, mem_singleton, h2, decide_eq_decide]
  constructor
  · rintro (h | h)
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · rintro (h | h)
    · left; exact_mod_cast h
    · right; rw [h]; push_cast; ring

theorem nisanBS_upper (m : ℕ) (hm : 2 ≤ m) (x : Fin (4 * m) → Bool)
    (cB : Finset (Finset (Fin (4 * m))))
    (hv : IsValidBlockConfig (nisanExample (4 * m)) x cB) : #cB ≤ 3 * m := by
  obtain ⟨hd, hs⟩ := hv
  have hwz := nisanBS_weight_add x
  have hblock : ∀ B ∈ cB, ∃ w', w' + #(B.filter (fun i => x i = true)) =
      #{i | x i = true} + #(B.filter (fun i => x i = false)) ∧
      ¬((w' = 2 * m ∨ w' = 2 * m + 1) ↔
        (#{i | x i = true} = 2 * m ∨ #{i | x i = true} = 2 * m + 1)) := by
    intro B hB
    refine ⟨_, nisanBS_flip_weight x B, ?_⟩
    have := hs B hB
    rw [nisanBS_val, nisanBS_val] at this
    intro hiff
    exact this (decide_eq_decide.mpr hiff)
  have hcard := nisanBS_card_le x cB hd
  generalize #{i | x i = true} = w at hblock hwz hcard
  generalize #{i | x i = false} = z at hwz hcard
  obtain ⟨α, β, h1, h2⟩ : ∃ α β : ℕ, (∀ a b w' : ℕ, w' + a = w + b →
      ¬((w' = 2 * m ∨ w' = 2 * m + 1) ↔ (w = 2 * m ∨ w = 2 * m + 1)) → 2 ≤ α * a + β * b) ∧
      α * w + β * z ≤ 6 * m := by
    rcases (show w = 2 * m ∨ w = 2 * m + 1 ∨ w + 1 = 2 * m ∨ w + 2 ≤ 2 * m ∨
        w = 2 * m + 2 ∨ 2 * m + 3 ≤ w by omega) with h | h | h | h | h | h
    · exact ⟨2, 1, fun a b w' e hne => by omega, by omega⟩
    · exact ⟨1, 2, fun a b w' e hne => by omega, by omega⟩
    · exact ⟨0, 2, fun a b w' e hne => by omega, by omega⟩
    · exact ⟨0, 1, fun a b w' e hne => by omega, by omega⟩
    · exact ⟨2, 0, fun a b w' e hne => by omega, by omega⟩
    · exact ⟨1, 0, fun a b w' e hne => by omega, by omega⟩
  have := hcard α β (fun B hB => by
    obtain ⟨w', e, hne⟩ := hblock B hB
    exact h1 _ _ w' e hne)
  omega

theorem nisanBS_lower (m : ℕ) (hm : 1 ≤ m) :
    3 * m ≤ blockSensitivity (nisanExample (4 * m)) := by
  let x : Fin (4 * m) → Bool := fun i => decide (i.val < 2 * m)
  let g : Fin (4 * m) → ℕ := fun i => if i.val < 2 * m then i.val else (i.val + 2 * m) / 2
  let cB : Finset (Finset (Fin (4 * m))) :=
    (range (3 * m)).image (fun l => univ.filter (fun i => g i = l))
  have hpre : ∀ l < 3 * m, ∃ i : Fin (4 * m), g i = l := by
    intro l hl
    by_cases h : l < 2 * m
    · exact ⟨⟨l, by omega⟩, by simp [g, h]⟩
    · refine ⟨⟨2 * l - 2 * m, by omega⟩, ?_⟩
      simp only [g]
      rw [if_neg (by simp; omega)]
      omega
  have hcard : #cB = 3 * m := by
    rw [card_image_of_injOn, card_range]
    intro l₁ hl₁ l₂ hl₂ heq
    simp only [coe_range, Set.mem_Iio] at hl₁ hl₂
    obtain ⟨i, hi⟩ := hpre l₁ hl₁
    have hmem : i ∈ univ.filter (fun i => g i = l₁) := by simp [hi]
    simp only at heq
    rw [heq] at hmem
    simp at hmem
    omega
  have hw : #{i | x i = true} = 2 * m := by
    simp only [x, decide_eq_true_eq]
    rw [Fin.card_filter_val_lt]
    omega
  have hvalid : IsValidBlockConfig (nisanExample (4 * m)) x cB := by
    constructor
    · intro B₁ hB₁ B₂ hB₂ hne
      simp only [cB, coe_image, coe_range, Set.mem_image, Set.mem_Iio] at hB₁ hB₂
      obtain ⟨l₁, -, rfl⟩ := hB₁
      obtain ⟨l₂, -, rfl⟩ := hB₂
      rw [Function.onFun, id, id, Finset.disjoint_left]
      intro i h₁ h₂
      simp only [mem_filter, mem_univ, true_and] at h₁ h₂
      subst h₁; subst h₂
      exact hne rfl
    · intro B hB
      simp only [cB, mem_image, mem_range] at hB
      obtain ⟨l, hl, rfl⟩ := hB
      have hfw := nisanBS_flip_weight x (univ.filter (fun i => g i = l))
      rw [nisanBS_val, nisanBS_val, hw]
      intro heq
      rw [decide_eq_decide] at heq
      rw [hw] at hfw
      by_cases h : l < 2 * m
      · have hb : #((univ.filter (fun i => g i = l)).filter (fun i => x i = false)) = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]
          intro i hi
          simp only [mem_filter, mem_univ, true_and, g] at hi
          simp only [x, decide_eq_false_iff_not, not_not]
          split_ifs at hi with h'
          · exact h'
          · omega
        have ha : 0 < #((univ.filter (fun i => g i = l)).filter (fun i => x i = true)) := by
          rw [card_pos]
          refine ⟨⟨l, by omega⟩, ?_⟩
          simp [g, x, h]
        omega
      · have ha : #((univ.filter (fun i => g i = l)).filter (fun i => x i = true)) = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]
          intro i hi
          simp only [mem_filter, mem_univ, true_and, g] at hi
          simp only [x, decide_eq_true_eq]
          split_ifs at hi with h'
          · omega
          · exact h'
        have hb : 1 < #((univ.filter (fun i => g i = l)).filter (fun i => x i = false)) := by
          rw [one_lt_card]
          refine ⟨⟨2 * l - 2 * m, by omega⟩, ?_, ⟨2 * l - 2 * m + 1, by omega⟩, ?_, ?_⟩
          · simp only [mem_filter, mem_univ, true_and, g, x]
            rw [if_neg (by simp; omega)]
            simp; omega
          · simp only [mem_filter, mem_univ, true_and, g, x]
            rw [if_neg (by simp; omega)]
            simp; omega
          · simp [Fin.ext_iff]
        omega
  calc 3 * m = #cB := hcard.symm
    _ ≤ blockSensitivityAt (nisanExample (4 * m)) x := by
        unfold blockSensitivityAt
        exact le_sup (f := card) (by simpa using hvalid)
    _ ≤ blockSensitivity (nisanExample (4 * m)) := le_sup (f := blockSensitivityAt _) (mem_univ x)

theorem nisanExample_blockSensitivity (n : ℕ) (hn : 4 ∣ n) (hn_large : 8 ≤ n) :
    blockSensitivity (nisanExample n) = 3 * n / 4 := by
  obtain ⟨m, rfl⟩ := hn
  have hm : 2 ≤ m := by omega
  rw [show 3 * (4 * m) / 4 = 3 * m by omega]
  refine le_antisymm ?_ (nisanBS_lower m (by omega))
  unfold blockSensitivity
  refine Finset.sup_le fun x _ => ?_
  unfold blockSensitivityAt
  refine Finset.sup_le fun cB hcB => ?_
  exact nisanBS_upper m hm x cB (by simpa using hcB)

end OpenProofs.StrongSensitivityConjecture
