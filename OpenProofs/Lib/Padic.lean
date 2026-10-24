import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Shared helpers: p-adic valuations of finite sums

Reusable, fully proved lemmas for results. Same rules as result files (see AGENTS.md "Shared
helper library").
-/

namespace OpenProofs.Lib

/-- If every term of a finite sum of rationals has `p`-adic valuation `> c` for some `c < 0`,
then so does the sum. Unlike Mathlib's `padicValRat.lt_sum_of_lt`, terms may be zero and the sum
may vanish (the zero sum has valuation `0 > c`). -/
theorem lt_padicValRat_sum_of_forall_lt (p : ℕ) [Fact p.Prime] (c : ℤ) (hc : c < 0)
    (F : ℕ → ℚ) (S : Finset ℕ) (h : ∀ i ∈ S, c < padicValRat p (F i)) :
    c < padicValRat p (∑ i ∈ S, F i) := by
  induction S using Finset.induction_on with
  | empty => simpa using hc
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    by_cases h0 : F a + ∑ i ∈ S, F i = 0
    · rw [h0, padicValRat.zero]
      exact hc
    · exact lt_of_lt_of_le (lt_min (h a (Finset.mem_insert_self a S))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
        (padicValRat.min_le_padicValRat_add h0)

end OpenProofs.Lib
