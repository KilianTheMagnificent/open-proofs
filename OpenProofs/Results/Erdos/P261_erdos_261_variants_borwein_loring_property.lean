import FormalConjectures.ErdosProblems.«261»

/-!
# `Erdos261.erdos_261.variants.borwein_loring_property`

Upstream: `Erdos261.erdos_261.variants.borwein_loring_property` (category textbook), `FormalConjectures/ErdosProblems/261.lean` line 66.
Proof idea: telescoping gives `∑_{a < k ≤ a + j} k / 2^k = (a + 2) / 2^a - (a + j + 2) / 2^(a + j)`
(induction on `j`). With `n = 2^(m+1) - m - 2` we have `n + m + 2 = 2^(m+1)`, so the subtracted
term is `2 / 2^n` and the sum equals `n / 2^n`. Take `t = m ≥ 2` and `a i = n + 1 + i`.
-/

open scoped Cardinal
open Erdos261

namespace OpenProofs.Erdos261

lemma op261_telescope (a j : ℕ) :
    ∑ i ∈ Finset.range j, ((a + 1 + i : ℕ) : ℚ) / (2 : ℚ) ^ (a + 1 + i) =
      ((a : ℚ) + 2) / 2 ^ a - ((a : ℚ) + j + 2) / 2 ^ (a + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (2 : ℚ) ^ (a + 1 + j) = 2 ^ (a + j) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have h2 : (2 : ℚ) ^ (a + (j + 1)) = 2 ^ (a + j) * 2 := by
      rw [← pow_succ, Nat.add_assoc]
    rw [h1, h2]
    push_cast
    field_simp
    ring

theorem erdos_261.variants.borwein_loring_property (m : ℕ) (hm : 2 ≤ m) :
    Erdos261Prop (2 ^ (m + 1) - m - 2) := by
  have hlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  set n := 2 ^ (m + 1) - m - 2 with hn
  have hn2 : n + m + 2 = 2 ^ (m + 1) := by omega
  refine ⟨m, hm, fun i => n + 1 + i, ?_, ?_, ?_⟩
  · intro i j h
    simp only at h
    exact Fin.ext (by omega)
  · intro i
    simp only [Pi.one_apply]
    omega
  · rw [Fin.sum_univ_eq_sum_range (fun i => ((n + 1 + i : ℕ) : ℚ) / (2 : ℚ) ^ (n + 1 + i)) m,
      op261_telescope]
    have hq : (n : ℚ) + m + 2 = 2 ^ (m + 1) := by exact_mod_cast hn2
    rw [hq, pow_add, pow_succ]
    field_simp
    ring

end OpenProofs.Erdos261
