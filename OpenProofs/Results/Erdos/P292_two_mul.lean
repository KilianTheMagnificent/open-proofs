import FormalConjectures.ErdosProblems.«292»

/-!
# Erdős 292: `erdos_292.variants.two_mul`

Upstream: `Erdos292.erdos_292.variants.two_mul`. van Doorn's observation: if `n ∈ A` with
`1 < n`, witnessed by `S ⊆ [1, n]` with `n ∈ S` and `∑ 1/m = 1`, then `{2} ∪ 2·S` witnesses
`2 * n ∈ A`, since `1/2 + ∑ 1/(2m) = 1/2 + 1/2 = 1`. The union is disjoint because `1 ∉ S`:
if `1 ∈ S` then the remaining terms (which include `1/n > 0`) would have to sum to `0`.
-/

open Erdos292

namespace OpenProofs.Erdos292

theorem erdos_292.variants.two_mul : ∀ n ∈ A, 1 < n → 2 * n ∈ A := by
  rintro n ⟨S, hSsub, hnS, hsum⟩ hn
  have h1 : 1 ∉ S := by
    intro h1S
    have hne : n ∈ S.erase 1 := Finset.mem_erase.mpr ⟨by omega, hnS⟩
    have hpos : 0 < ∑ m ∈ S.erase 1, (1 : ℚ) / m := by
      apply Finset.sum_pos'
      · intro i _
        positivity
      · refine ⟨n, hne, ?_⟩
        have : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
        positivity
    rw [← Finset.add_sum_erase S _ h1S] at hsum
    have h11 : (1 : ℚ) / ((1 : ℕ) : ℚ) = 1 := by simp
    linarith
  refine ⟨insert 2 (S.image (2 * ·)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨m, hm, rfl⟩
    · simp only [Finset.mem_Icc]
      omega
    · have := Finset.mem_Icc.mp (hSsub hm)
      simp only [Finset.mem_Icc]
      omega
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hnS)
  · have h2 : 2 ∉ S.image (2 * ·) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro m hm h
      have : m = 1 := by omega
      exact h1 (this ▸ hm)
    rw [Finset.sum_insert h2, Finset.sum_image (by intro a _ b _ h; simpa using h)]
    have : ∑ m ∈ S, (1 : ℚ) / ((2 * m : ℕ) : ℚ) = (1 / 2) * ∑ m ∈ S, (1 : ℚ) / m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      rw [one_div_mul_one_div]
    rw [this, hsum]
    norm_num

end OpenProofs.Erdos292
