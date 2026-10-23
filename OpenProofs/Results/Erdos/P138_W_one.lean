import FormalConjectures.ErdosProblems.«138»

/-!
# Erdős 138: `monoAPNumber_two_one`

Upstream: `Erdos138.monoAPNumber_two_one` (category test): `W 1 = 1`.

An arithmetic progression of length `1` is a singleton. For `N ≥ 1`, the singleton `{1}` of
`Finset.Icc 1 N` is a monochromatic one under every colouring. For `N = 0` the domain
`Finset.Icc 1 0` is empty, so the only subset is `∅`, whose image is not a singleton. Hence the
defining set `monoAP_guarantee_set 2 1` is `Set.Ici 1`, and its infimum is `1`.
-/

open Erdos138

namespace OpenProofs.Erdos138

/-- Membership in `monoAP_guarantee_set 2 1` is exactly `1 ≤ N`. -/
theorem mem_iff_P138 (N : ℕ) : N ∈ monoAP_guarantee_set 2 1 ↔ 1 ≤ N := by
  unfold monoAP_guarantee_set ContainsMonoAPofLength
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    by_contra hN
    obtain ⟨c, ap, hap, -⟩ := h (fun _ => 0)
    have hN0 : N = 0 := by omega
    subst hN0
    have : ap = ∅ := by
      ext ⟨x, hx⟩
      simp at hx
    subst this
    simp at hap
  · intro hN coloring
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := by simp; omega
    refine ⟨coloring ⟨1, h1⟩, {⟨1, h1⟩}, ?_, ?_⟩
    · simp
    · simp

theorem monoAPNumber_two_one : W 1 = 1 := by
  show sInf (monoAP_guarantee_set 2 1) = 1
  have : monoAP_guarantee_set 2 1 = Set.Ici 1 := by
    ext N
    rw [mem_iff_P138]
    rfl
  rw [this]
  exact csInf_Ici

end OpenProofs.Erdos138
