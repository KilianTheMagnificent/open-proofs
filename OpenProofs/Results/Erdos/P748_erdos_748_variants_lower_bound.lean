import FormalConjectures.ErdosProblems.«748»

/-!
# `Erdos748.erdos_748.variants.lower_bound`

Upstream: `Erdos748.erdos_748.variants.lower_bound` (category textbook), `FormalConjectures/ErdosProblems/748.lean` line 67.
Proof idea: every subset of `(n/2, n] = Icc (n/2 + 1) n` is sum-free (the sum of two
elements exceeds `n`), so `f n ≥ 2 ^ (n - n/2)` and `n - n/2 ≥ n/2` as real numbers.
-/

open Filter Real
open Erdos748

namespace OpenProofs.Erdos748

theorem erdos_748_lower_bound_nat (n : ℕ) : 2 ^ (n - n / 2) ≤ f n := by
  classical
  unfold f
  have hsub : (Finset.Icc (n / 2 + 1) n).powerset ⊆
      (Finset.Icc 1 n).powerset.filter fun A : Finset ℕ ↦ IsSumFree (A : Set ℕ) := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hA.trans (Finset.Icc_subset_Icc (by omega) le_rfl), ?_⟩
    rw [isSumFree_iff]
    intro x hx y hy hxy
    have hx' := Finset.mem_Icc.mp (hA hx)
    have hy' := Finset.mem_Icc.mp (hA hy)
    have hxy' := Finset.mem_Icc.mp (hA hxy)
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_powerset, Nat.card_Icc] at this
  convert this using 2
  omega

theorem erdos_748.variants.lower_bound (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (f n : ℝ) := by
  have h := erdos_748_lower_bound_nat n
  have h2 : ((2 : ℕ) ^ (n - n / 2) : ℝ) ≤ (f n : ℝ) := by exact_mod_cast h
  refine le_trans ?_ h2
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (n : ℝ) ≤ 2 * ((n - n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n - n / 2) := by omega
    exact_mod_cast this
  linarith

end OpenProofs.Erdos748
