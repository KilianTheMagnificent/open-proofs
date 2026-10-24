import FormalConjectures.ErdosProblems.«44»

/-!
# `Erdos44.greedy_sidon_construction`

Upstream: `Erdos44.greedy_sidon_construction` (category textbook), `FormalConjectures/ErdosProblems/44.lean` line 138.
Proof idea: take a Sidon subset `A` of `{1, …, N}` of maximal cardinality. For `x ∈ {1, …, N}`
not in `A`, `insert x A` is not Sidon, so `x + a = b + c` or `2x = b + c` for some `a, b, c ∈ A`.
Hence every element of `{1, …, N}` is a value of the map
`f (a, b, c) = if a = b then (a + c) / 2 else b + c - a` on `A × A × A`, so `N ≤ |A|³`.
-/

open Function Set Finset
open Erdos44

namespace OpenProofs.Erdos44

theorem greedy_sidon_construction (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ N ≤ A.card ^ 3 := by
  classical
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image
    ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ))
    Finset.card ⟨∅, by simp [IsSidon]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hsub, hsid⟩ := hA
  refine ⟨A, hsub, hsid, ?_⟩
  let f : ℕ × ℕ × ℕ → ℕ := fun p ↦
    if p.1 = p.2.1 then (p.1 + p.2.2) / 2 else p.2.1 + p.2.2 - p.1
  have hcover : Finset.Icc 1 N ⊆ (A ×ˢ A ×ˢ A).image f := by
    intro x hx
    rw [Finset.mem_image]
    by_cases hxA : x ∈ A
    · exact ⟨(x, x, x), by simp [hxA], by simp only [f, if_true]; omega⟩
    · have hns : ¬ IsSidon ((insert x A : Finset ℕ) : Set ℕ) := by
        intro hs
        have := hmax (insert x A) (by
          simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.insert_subset hx hsub, hs⟩)
        rw [Finset.card_insert_of_notMem hxA] at this
        omega
      have h3 : ∀ a ∈ A, a ≠ x := by
        rintro a ha rfl
        exact hxA ha
      have h1 : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, x + a = b + c →
          ∃ p ∈ A ×ˢ A ×ˢ A, f p = x := by
        intro a ha b hb c hc h
        have hab : a ≠ b := by
          rintro rfl
          exact h3 c hc (by omega)
        exact ⟨(a, b, c), by simp [ha, hb, hc], by simp only [f, hab, if_false]; omega⟩
      have h2 : ∀ b ∈ A, ∀ c ∈ A, x + x = b + c → ∃ p ∈ A ×ˢ A ×ˢ A, f p = x := by
        intro b hb c hc h
        exact ⟨(b, b, c), by simp [hb, hc], by simp only [f, if_true]; omega⟩
      simp only [IsSidon, not_forall] at hns
      obtain ⟨i1, hi1, j1, hj1, i2, hi2, j2, hj2, hsum, hne⟩ := hns
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi1 hj1 hi2 hj2
      rcases hi1 with rfl | hi1 <;> rcases hj1 with rfl | hj1 <;>
        rcases hi2 with rfl | hi2 <;> rcases hj2 with rfl | hj2
      all_goals first
        | exact absurd (hsid _ hi1 _ hj1 _ hi2 _ hj2 hsum) hne
        | exact h1 _ hi2 _ hj1 _ hj2 (by omega)
        | exact h1 _ hi1 _ hj1 _ hj2 (by omega)
        | exact h1 _ hj2 _ hi1 _ hi2 (by omega)
        | exact h1 _ hj1 _ hi1 _ hi2 (by omega)
        | exact h2 _ hj1 _ hj2 (by omega)
        | exact h2 _ hi1 _ hi2 (by omega)
        | exact (hne (by omega)).elim
  calc N = (Finset.Icc 1 N).card := by simp
    _ ≤ ((A ×ˢ A ×ˢ A).image f).card := Finset.card_le_card hcover
    _ ≤ (A ×ˢ A ×ˢ A).card := Finset.card_image_le
    _ = A.card ^ 3 := by simp [Finset.card_product]; ring

end OpenProofs.Erdos44
