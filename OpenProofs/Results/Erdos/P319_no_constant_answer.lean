import FormalConjectures.ErdosProblems.«319»

/-!
# Erdős 319: no `N`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos319.erdos_319.no_constant_answer`.

Upstream `Erdos319.erdos_319 (N : ℕ)` asserts that one constant is the maximum for every `N`.
For `N = 1` every admissible set has at most one element, while for `N = 6` the set `{2, 3, 6}`
with signs `+, -, -` is admissible (`1/2 - 1/3 - 1/6 = 0`, and no proper nonempty subsum
vanishes). So the maximum is `≤ 1` at `N = 1` and `≥ 3` at `N = 6`.
-/

namespace OpenProofs.Erdos319

open scoped Finset in
theorem erdos_319.no_constant_answer : ∀ a : ℕ, ¬ ∀ N : ℕ, IsGreatest
    { #A | (A) (_ : A ⊆ Finset.Icc 1 N)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) } a := by
  intro a h
  obtain ⟨A, hA, -, hcard⟩ := (h 1).1
  have hle : #A ≤ 1 := by
    have := Finset.card_le_card hA
    simpa using this
  have h3 : 3 ∈ { #A | (A) (_ : A ⊆ Finset.Icc 1 6)
      (_ : ∃ δ : ℕ → ℤˣ, ∑ n ∈ A, (δ n : ℚ) / n = 0 ∧
        ∀ A' ⊂ A, A'.Nonempty → ∑ n ∈ A', (δ n : ℚ) / n ≠ 0) } := by
    refine ⟨{2, 3, 6}, by decide, ⟨fun n => if n = 2 then 1 else -1, ?_, ?_⟩, by decide⟩
    · simp
      norm_num
    · intro A' hA' hne
      have hmem : A' ∈ ({2, 3, 6} : Finset ℕ).powerset := Finset.mem_powerset.2 hA'.1
      have hne' : A' ≠ {2, 3, 6} := hA'.ne
      simp [Finset.powerset_insert] at hmem
      rcases hmem with (rfl | rfl) | (rfl | rfl) | ⟨b, ((rfl | rfl) | rfl | rfl), rfl⟩
      all_goals first
        | (exact absurd rfl hne')
        | (simp at hne; done)
        | (simp; norm_num)
        | (norm_num [Finset.sum_pair])
  have := (h 6).2 h3
  omega

end OpenProofs.Erdos319
