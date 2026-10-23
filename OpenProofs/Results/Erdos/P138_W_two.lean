import FormalConjectures.ErdosProblems.«138»

/-!
# Erdős 138: `monoAPNumber_two_two`

Upstream: `Erdos138.monoAPNumber_two_two` (category test): `W 2 = 3`.

Any two distinct naturals `a < b` form an arithmetic progression of length `2`
(`Nat.isAPOfLength_pair`). For `N ≥ 3`, two of the colours of `1, 2, 3` agree (pigeonhole on
`Fin 2`), giving a monochromatic progression of length `2`. For `N ≤ 2`, colour `1` with `0` and
everything else with `1`: a progression of length `2` has two distinct terms in `{1, 2}`, so it is
`{1, 2}`, which is not monochromatic. Hence `monoAP_guarantee_set 2 2 = Set.Ici 3`.
-/

open Erdos138

namespace OpenProofs.Erdos138

/-- Two equally coloured distinct points form a monochromatic AP of length two. -/
theorem mono_pair_P138 {N : ℕ} (coloring : Finset.Icc 1 N → Fin 2) (a b : ℕ)
    (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N) (hab : a < b)
    (hc : coloring ⟨a, ha⟩ = coloring ⟨b, hb⟩) : ContainsMonoAPofLength coloring 2 := by
  refine ⟨coloring ⟨a, ha⟩, {⟨a, ha⟩, ⟨b, hb⟩}, ?_, ?_⟩
  · rw [Set.image_pair]
    exact_mod_cast Nat.isAPOfLength_pair hab
  · rintro m (rfl | rfl)
    · rfl
    · exact hc.symm

/-- Every `N ≥ 3` forces a monochromatic progression of length two. -/
theorem three_mem_P138 (N : ℕ) (hN : 3 ≤ N) : N ∈ monoAP_guarantee_set 2 2 := by
  intro coloring
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := by simp; omega
  have h2 : (2 : ℕ) ∈ Finset.Icc 1 N := by simp; omega
  have h3 : (3 : ℕ) ∈ Finset.Icc 1 N := by simp; omega
  have key : ∀ x y z : Fin 2, x = y ∨ x = z ∨ y = z := by decide
  rcases key (coloring ⟨1, h1⟩) (coloring ⟨2, h2⟩) (coloring ⟨3, h3⟩) with h | h | h
  · exact mono_pair_P138 coloring 1 2 h1 h2 (by norm_num) h
  · exact mono_pair_P138 coloring 1 3 h1 h3 (by norm_num) h
  · exact mono_pair_P138 coloring 2 3 h2 h3 (by norm_num) h

/-- For `N ≤ 2`, colouring `1` differently from everything else avoids such progressions. -/
theorem not_mem_P138 (N : ℕ) (hN : N ≤ 2) : N ∉ monoAP_guarantee_set 2 2 := by
  intro h
  obtain ⟨c, ap, hap, hcol⟩ := h (fun x => if x.1 = 1 then 0 else 1)
  have hcard : ((·.1) '' ap : Set ℕ).encard = 2 := by
    have := hap.card
    exact_mod_cast this
  obtain ⟨x, y, hxy, hs⟩ := Set.encard_eq_two.1 hcard
  have hx : x ∈ ((·.1) '' ap : Set ℕ) := by rw [hs]; simp
  have hy : y ∈ ((·.1) '' ap : Set ℕ) := by rw [hs]; simp
  obtain ⟨⟨x', hx'N⟩, hx'ap, rfl⟩ := hx
  obtain ⟨⟨y', hy'N⟩, hy'ap, rfl⟩ := hy
  have cx := hcol _ hx'ap
  have cy := hcol _ hy'ap
  have hx'' : 1 ≤ x' ∧ x' ≤ N := by simpa using hx'N
  have hy'' : 1 ≤ y' ∧ y' ≤ N := by simpa using hy'N
  have : x' = 1 ∨ x' = 2 := by omega
  have : y' = 1 ∨ y' = 2 := by omega
  rcases this with rfl | rfl <;> rcases ‹x' = 1 ∨ x' = 2› with rfl | rfl
  · exact hxy rfl
  · exact absurd (cx.trans cy.symm) (by simp)
  · exact absurd (cx.trans cy.symm) (by simp)
  · exact hxy rfl

theorem monoAPNumber_two_two : W 2 = 3 := by
  show sInf (monoAP_guarantee_set 2 2) = 3
  have : monoAP_guarantee_set 2 2 = Set.Ici 3 := by
    ext N
    constructor
    · intro h
      by_contra hN
      exact not_mem_P138 N (by simp at hN; omega) h
    · exact three_mem_P138 N
  rw [this]
  exact csInf_Ici

end OpenProofs.Erdos138
