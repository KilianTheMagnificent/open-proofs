import FormalConjectures.ErdosProblems.«261»

/-!
# `Erdos261.erdos_261.variants.borwein_loring`

Upstream: `Erdos261.erdos_261.variants.borwein_loring` (category textbook), `FormalConjectures/ErdosProblems/261.lean` line 58.
Proof idea: by induction on `m`, `∑_{a < k ≤ a + m} k / 2^k = (a + 2) / 2^a - (a + m + 2) / 2^(a + m)`
(the step is `2 (b + 2) - (b + 3) = b + 1` over `2^(b+1)`). With `n = 2^(m+1) - m - 2` we have
`n + m + 2 = 2^(m+1)` (since `m + 2 ≤ 2^(m+1)`), so the right side is
`(n + 2) / 2^n - 2^(m+1) / 2^(n+m) = (n + 2) / 2^n - 2 / 2^n = n / 2^n`.
-/

open scoped Cardinal
open Erdos261

namespace OpenProofs.Erdos261

theorem bl261_sum_Ioc (a m : ℕ) :
    ∑ k ∈ Finset.Ioc a (a + m), (k : ℚ) / 2 ^ k
      = ((a : ℚ) + 2) / 2 ^ a - ((a : ℚ) + m + 2) / 2 ^ (a + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), ih]
    push_cast
    rw [pow_succ]
    field_simp
    ring

theorem erdos_261.variants.borwein_loring (m : ℕ) (hm : 0 < m) :
    let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ) := by
  intro n
  rw [bl261_sum_Ioc]
  have hle : m + 2 ≤ 2 ^ (m + 1) := by
    have := Nat.lt_two_pow_self (n := m)
    rw [pow_succ]
    omega
  have hn : (n : ℚ) + m + 2 = 2 ^ (m + 1) := by
    have : n + m + 2 = 2 ^ (m + 1) := by omega
    exact_mod_cast this
  rw [hn, pow_add]
  field_simp
  ring

end OpenProofs.Erdos261
