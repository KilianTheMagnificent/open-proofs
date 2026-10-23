import FormalConjectures.ErdosProblems.«292»

/-!
# Erdős 292: `erdos_292.variants.mul`

Upstream: `Erdos292.erdos_292.variants.mul`. Straus's observation: if `S ⊆ [1, m]` with
`m ∈ S` and `T ⊆ [1, n]` with `n ∈ T` both have reciprocal sum `1`, then
`(S \ {m}) ∪ m·T ⊆ [1, mn]` contains `mn` and has reciprocal sum
`(1 - 1/m) + (1/m)·1 = 1`. The union is disjoint because every element of `S \ {m}` is `< m`
while every element of `m·T` is `≥ m`.
-/

open Erdos292

namespace OpenProofs.Erdos292

theorem erdos_292.variants.mul : ∀ m ∈ A, ∀ n ∈ A, m * n ∈ A := by
  rintro m ⟨S, hSsub, hmS, hSsum⟩ n ⟨T, hTsub, hnT, hTsum⟩
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hSsub hmS)).1
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (hTsub hnT)).1
  have hdisj : Disjoint (S.erase m) (T.image (m * ·)) := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    obtain ⟨hxm, hxS⟩ := Finset.mem_erase.mp hxS
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp hxT
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp (hTsub hbT)).1
    have hxle : m * b ≤ m := (Finset.mem_Icc.mp (hSsub hxS)).2
    have : m ≤ m * b := Nat.le_mul_of_pos_right m hb1
    exact hxm (le_antisymm hxle this)
  refine ⟨S.erase m ∪ T.image (m * ·), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨_, hxS⟩ := Finset.mem_erase.mp hx
      have := Finset.mem_Icc.mp (hSsub hxS)
      have : m ≤ m * n := Nat.le_mul_of_pos_right m hn1
      simp only [Finset.mem_Icc]
      omega
    · obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp hx
      have hb := Finset.mem_Icc.mp (hTsub hbT)
      simp only [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul_left m hb.2⟩
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hnT)
  · rw [Finset.sum_union hdisj,
      Finset.sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by omega) h)]
    have hS' : ∑ x ∈ S.erase m, (1 : ℚ) / x = 1 - 1 / m := by
      rw [← Finset.add_sum_erase S _ hmS] at hSsum
      linarith
    have hT' : ∑ b ∈ T, (1 : ℚ) / ((m * b : ℕ) : ℚ) = (1 / m) * ∑ b ∈ T, (1 : ℚ) / b := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      push_cast
      rw [one_div_mul_one_div]
    rw [hS', hT', hTsum]
    ring

end OpenProofs.Erdos292
