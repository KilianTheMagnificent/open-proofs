import FormalConjectures.ErdosProblems.«450»

/-!
# Erdős 450: no `(ε, n)`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos450.erdos_450.no_constant_answer`.

Upstream `Erdos450.erdos_450 (ε : ℝ) (hε : 0 < ε) (n : ℕ)` asserts that `windowThreshold ε n` is
one constant. For `ε = 1` every window is sparse (it has fewer than `y` integers), so
`windowThreshold 1 2 = 0`. For `ε = 1/4` and `n = 2` the window `(2, 4) = {3}` contains `3`, which
has the divisor `3 ∈ (2, 4)`, and `1 > 2/4`; so `windowThreshold (1/4) 2 ≠ 0`.
-/

open Erdos450

namespace OpenProofs.Erdos450

open scoped Classical in
theorem erdos_450.no_constant_answer :
    ∀ a : ℕ∞, ¬ ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, windowThreshold ε n = a := by
  intro a h
  have t1 : windowThreshold 1 2 = 0 := by
    apply le_antisymm _ (by simp)
    refine iInf_le_of_le ⟨0, fun z _ x => ?_⟩ (by simp)
    unfold localCount
    have h1 := Finset.card_filter_le (Finset.Ioo x (x + z)) (HasMediumDivisor 2)
    have h2 : (Finset.Ioo x (x + z)).card ≤ z := by simp
    have : ((Finset.Ioo x (x + z)).filter (HasMediumDivisor 2)).card ≤ z := h1.trans h2
    simp only [one_mul]
    exact_mod_cast this
  have t2 : windowThreshold (1 / 4) 2 ≠ 0 := by
    intro h0
    rw [windowThreshold, ← bot_eq_zero, iInf_eq_bot] at h0
    obtain ⟨⟨y, hy⟩, hlt⟩ := h0 1 (by simp)
    have hy0 : y = 0 := by
      have : (y : ℕ∞) < 1 := hlt
      exact_mod_cast Order.lt_one_iff.1 this
    subst hy0
    have := hy 2 (by simp) 2
    have hc : localCount 2 2 2 = 1 := by
      unfold localCount
      have : (Finset.Ioo 2 (2 + 2)).filter (HasMediumDivisor 2) = {3} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_singleton, HasMediumDivisor]
        constructor
        · rintro ⟨⟨h1, h2⟩, -⟩
          omega
        · rintro rfl
          exact ⟨by norm_num, 3, by norm_num, by norm_num, dvd_refl 3⟩
      rw [this, Finset.card_singleton]
    rw [hc] at this
    norm_num at this
  exact t2 ((h (1 / 4) (by norm_num) 2).trans ((h 1 one_pos 2).symm.trans t1))

end OpenProofs.Erdos450
