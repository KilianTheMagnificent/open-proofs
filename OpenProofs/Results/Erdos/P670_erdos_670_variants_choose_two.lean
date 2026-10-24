import FormalConjectures.ErdosProblems.«670»

/-!
# `Erdos670.erdos_670.variants.choose_two`

Upstream: `Erdos670.erdos_670.variants.choose_two` (category textbook), `FormalConjectures/ErdosProblems/670.lean` line 82.
Proof idea: for `n ≤ 1` the binomial coefficient is `0` and the diameter is nonnegative. For
`n ≥ 3`, any two distinct points `a, b` have a third point `c`, and
`1 ≤ |d(a, c) - d(b, c)| ≤ d(a, b)`, so every distance is at least `1`. The unordered pairs of
distinct points (there are `n.choose 2` of them) get distances that are at least `1` and pairwise
at least `1` apart; induction on the pair with the largest distance shows that a family of `m`
such values is bounded above only by numbers `≥ m`. The diameter bounds every distance.
-/

open Filter
open Erdos670

namespace OpenProofs.Erdos670

/-- A finite family of reals, all at least `1` and pairwise at least `1` apart, has all values
bounded only by numbers at least its size. -/
theorem erdos670_card_le_of_separated {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (T : Finset ι) :
    ∀ M : ℝ, 0 ≤ M → (∀ x ∈ T, 1 ≤ f x) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → 1 ≤ |f x - f y|) → (∀ x ∈ T, f x ≤ M) →
        (T.card : ℝ) ≤ M := by
  induction T using Finset.induction_on_max_value f with
  | empty => intro M hM _ _ _; simpa using hM
  | insert a s has hmax ih =>
    intro M hM h1 hsep hle
    have ha1 := h1 a (Finset.mem_insert_self a s)
    have key : (s.card : ℝ) ≤ f a - 1 := by
      apply ih (f a - 1) (by linarith)
      · intro x hx; exact h1 x (Finset.mem_insert_of_mem hx)
      · intro x hx y hy hxy
        exact hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      · intro x hx
        have hxa : x ≠ a := fun h => has (h ▸ hx)
        have h := hsep x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s) hxa
        have h2 := hmax x hx
        rw [abs_of_nonpos (by linarith)] at h
        linarith
    rw [Finset.card_insert_of_notMem has]
    push_cast
    have := hle a (Finset.mem_insert_self a s)
    linarith

theorem erdos_670.variants.choose_two (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d)))
    (hA : HasSeparatedDistances A) (hn : A.card ≠ 2) :
    (A.card.choose 2 : ℝ) ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  rcases Nat.lt_or_ge A.card 3 with h3 | h3
  · have h0 : A.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0]
    simpa using Metric.diam_nonneg
  · have hdist : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 ≤ dist a b := by
      intro a ha b hb hab
      obtain ⟨c, hc, hca, hcb⟩ : ∃ c ∈ A, c ≠ a ∧ c ≠ b := by
        by_contra hcon
        push Not at hcon
        have hsub : A ⊆ {a, b} := by
          intro c hc
          by_cases h : c = a
          · simp [h]
          · simp [hcon c hc h]
        have h1 := Finset.card_le_card hsub
        have h2 : ({a, b} : Finset _).card ≤ 2 := Finset.card_le_two
        omega
      have h := hA a ha c hc b hb c hc (Ne.symm hca) (Ne.symm hcb) (by
        intro h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hab h1
        · exact hca h1.symm)
      have := abs_dist_sub_le a b c
      linarith
    have hbdd : Bornology.IsBounded (A : Set (EuclideanSpace ℝ (Fin d))) := A.finite_toSet.isBounded
    let f : Sym2 (EuclideanSpace ℝ (Fin d)) → ℝ :=
      Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩
    have hcard := Sym2.card_image_offDiag A
    rw [← hcard]
    apply erdos670_card_le_of_separated f _ _ Metric.diam_nonneg
    · intro z hz
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_offDiag] at hp
      exact hdist a hp.1 b hp.2.1 hp.2.2
    · intro z hz w hw hzw
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨⟨c, e⟩, hq, rfl⟩ := Finset.mem_image.mp hw
      rw [Finset.mem_offDiag] at hp hq
      exact hA a hp.1 b hp.2.1 c hq.1 e hq.2.1 hp.2.2 hq.2.2 hzw
    · intro z hz
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_offDiag] at hp
      exact Metric.dist_le_diam_of_mem hbdd (Finset.mem_coe.mpr hp.1) (Finset.mem_coe.mpr hp.2.1)

end OpenProofs.Erdos670
