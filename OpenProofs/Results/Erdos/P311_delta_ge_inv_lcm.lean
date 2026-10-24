import FormalConjectures.ErdosProblems.«311»

/-!
# `Erdos311.delta_ge_inv_lcm`

Upstream: `Erdos311.delta_ge_inv_lcm` (category textbook), `FormalConjectures/ErdosProblems/311.lean` line 65.
Proof idea: let `L = [1, …, N]` (positive). The set defining `delta N` is nonempty (the empty
subset gives `1`), so it suffices to bound every element from below. For `A ⊆ {1, …, N}`, every
`n ∈ A` divides `L`, so `k = L - ∑_{n ∈ A} L / n` is an integer with `k = L * (1 - ∑ 1/n)`.
A non-zero value `|1 - ∑ 1/n|` forces `k ≠ 0`, hence `1 ≤ |k| = L * |1 - ∑ 1/n|`, i.e. the value
is at least `1 / L`; `le_csInf` concludes.
-/

open Finset Filter Topology
open Erdos311

namespace OpenProofs.Erdos311

theorem delta_ge_inv_lcm (N : ℕ) : 1 / (((Icc 1 N).lcm id : ℕ) : ℝ) ≤ delta N := by
  set L : ℕ := (Icc 1 N).lcm id with hL
  have hLpos : 0 < L := by
    apply Nat.pos_of_ne_zero
    rw [hL, Ne, Finset.lcm_eq_zero_iff]
    simp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  unfold delta
  apply le_csInf
  · exact ⟨1, one_ne_zero, ∅, empty_subset _, by simp⟩
  · rintro x ⟨hx, A, hA, rfl⟩
    have hdvd : ∀ n ∈ A, n ∣ L := fun n hn => Finset.dvd_lcm (hA hn)
    have hpos : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
    set k : ℤ := (L : ℤ) - ∑ n ∈ A, ((L / n : ℕ) : ℤ) with hk
    have hkR : (k : ℝ) = L * (1 - ∑ n ∈ A, (1 : ℝ) / n) := by
      rw [hk, mul_sub, mul_one, Finset.mul_sum]
      simp only [Int.cast_sub, Int.cast_natCast, Int.cast_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [Nat.cast_div (hdvd n hn) (Nat.cast_ne_zero.mpr (hpos n hn).ne')]
      ring
    have hk0 : k ≠ 0 := by
      intro h
      apply hx
      have h2 : (L : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) = 0 := by rw [← hkR, h]; simp
      rw [abs_eq_zero]
      rcases mul_eq_zero.mp h2 with h1 | h1
      · exact absurd h1 hLR.ne'
      · exact h1
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    rw [hkR, abs_mul, abs_of_pos hLR] at hk1
    rw [div_le_iff₀ hLR, mul_comm]
    exact hk1

end OpenProofs.Erdos311
