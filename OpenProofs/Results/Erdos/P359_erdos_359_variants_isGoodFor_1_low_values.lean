import FormalConjectures.ErdosProblems.«359»

/-!
# `Erdos359.erdos_359.variants.isGoodFor_1_low_values`

Upstream: `Erdos359.erdos_359.variants.isGoodFor_1_low_values` (category test), `FormalConjectures/ErdosProblems/359.lean` line 58.
Proof idea: let `L` be the concrete list `1, 2, 4, 5, 8, 10, 14, 15`. By induction on `j ≤ 6`,
if `A` agrees with `L` on `0, …, j`, the `IsLeast` clause of `IsGoodFor` forces
`A (j + 1) = L (j + 1)`: `L (j + 1)` is not a sum of a block of `L 0, …, L j` (so it lies in the
set), and every integer strictly between `L j` and `L (j + 1)` is such a block sum (so nothing
smaller lies in the set). Both facts about `L` are finite checks done by `decide`. The image of
`Set.Iic 7` is then read off.
-/

open Filter Asymptotics
open Erdos359

namespace OpenProofs.Erdos359

/-- The first eight terms `1, 2, 4, 5, 8, 10, 14, 15` (zero afterwards). -/
def lowSeq359 (i : ℕ) : ℕ := [1, 2, 4, 5, 8, 10, 14, 15].getD i 0

lemma lowSeq359_sum_congr (A : ℕ → ℕ) (j : ℕ) (hj : ∀ i ≤ j, A i = lowSeq359 i)
    (a b : ℕ) (hb : b ≤ j) :
    ∑ i ∈ Finset.Icc a b, A i = ∑ i ∈ Finset.Icc a b, lowSeq359 i := by
  refine Finset.sum_congr rfl fun i hi => hj i ?_
  rw [Finset.mem_Icc] at hi
  omega

lemma lowSeq359_step (A : ℕ → ℕ) (hA : IsGoodFor A 1) (j : ℕ)
    (hj : ∀ i ≤ j, A i = lowSeq359 i)
    (hv : lowSeq359 j < lowSeq359 (j + 1))
    (hmem : ∀ a ≤ j, ∀ b ≤ j, lowSeq359 (j + 1) ≠ ∑ i ∈ Finset.Icc a b, lowSeq359 i)
    (hlow : ∀ m < lowSeq359 (j + 1), lowSeq359 j < m →
      ∃ a ≤ j, ∃ b ≤ j, m = ∑ i ∈ Finset.Icc a b, lowSeq359 i) :
    ∀ i ≤ j + 1, A i = lowSeq359 i := by
  have hl := hA.2.2 j
  have hAj : A j = lowSeq359 j := hj j le_rfl
  have hle : A (j + 1) ≤ lowSeq359 (j + 1) := by
    refine hl.2 ⟨by omega, fun a b hab => ?_⟩
    by_cases h : a ≤ b
    · have hb : b ≤ j := by
        have := hab (Finset.mem_Icc.2 ⟨h, le_rfl⟩)
        simpa using this
      rw [lowSeq359_sum_congr A j hj a b hb]
      exact hmem a (by omega) b hb
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      omega
  have hge : lowSeq359 (j + 1) ≤ A (j + 1) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨h1, h2⟩ := hl.1
    obtain ⟨a, ha, b, hb, hsum⟩ := hlow (A (j + 1)) hlt (by omega)
    refine h2 a b ?_ (hsum.trans (lowSeq359_sum_congr A j hj a b hb).symm)
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only [Finset.mem_Iic]
    omega
  intro i hi
  rcases Nat.lt_or_eq_of_le hi with h | rfl
  · exact hj i (by omega)
  · omega

theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  have h0 : ∀ i ≤ 0, A i = lowSeq359 i := by
    intro i hi
    obtain rfl : i = 0 := by omega
    exact hA.1
  have h1 := lowSeq359_step A hA 0 h0 (by decide) (by decide) (by decide)
  have h2 := lowSeq359_step A hA 1 h1 (by decide) (by decide) (by decide)
  have h3 := lowSeq359_step A hA 2 h2 (by decide) (by decide) (by decide)
  have h4 := lowSeq359_step A hA 3 h3 (by decide) (by decide) (by decide)
  have h5 := lowSeq359_step A hA 4 h4 (by decide) (by decide) (by decide)
  have h6 := lowSeq359_step A hA 5 h5 (by decide) (by decide) (by decide)
  have h7 := lowSeq359_step A hA 6 h6 (by decide) (by decide) (by decide)
  ext y
  simp only [Set.mem_image, Set.mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [h7 x hx]
    interval_cases x <;> decide
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by decide, h7 0 (by decide)⟩
    · exact ⟨1, by decide, h7 1 (by decide)⟩
    · exact ⟨2, by decide, h7 2 (by decide)⟩
    · exact ⟨3, by decide, h7 3 (by decide)⟩
    · exact ⟨4, by decide, h7 4 (by decide)⟩
    · exact ⟨5, by decide, h7 5 (by decide)⟩
    · exact ⟨6, by decide, h7 6 (by decide)⟩
    · exact ⟨7, by decide, h7 7 (by decide)⟩

end OpenProofs.Erdos359
