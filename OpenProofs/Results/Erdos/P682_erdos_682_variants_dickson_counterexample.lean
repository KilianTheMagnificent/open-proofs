import FormalConjectures.ErdosProblems.«682»

/-!
# `Erdos682.erdos_682.variants.dickson_counterexample`

Upstream: `Erdos682.erdos_682.variants.dickson_counterexample` (category textbook), `FormalConjectures/ErdosProblems/682.lean` line 76.
Proof idea: every `m` strictly between `2183 + 30030 d` and `2201 + 30030 d` is
`(2183 + k) + 30030 d` with `1 ≤ k ≤ 17`, and each of `2184, …, 2200` has a prime factor
`q ≤ 13`, which also divides `30030`; so `q ∣ m` (checked by `omega` per case). Hence no such
`m` is prime and `m.minFac ≤ 13 < 18`. With `n = Nat.count Nat.Prime (2183 + 30030 d)`,
`Nat.nth_count` gives `p n = 2183 + 30030 d`, and since the count jumps by exactly one up to
`2201 + 30030 d`, also `p (n + 1) = 2201 + 30030 d`.
-/

open Filter Asymptotics
open Erdos682

namespace OpenProofs.Erdos682

theorem erdos_682.variants.dickson_counterexample (d : ℕ) (h₁ : (2183 + 30030 * d).Prime)
    (h₂ : (2201 + 30030 * d).Prime) : ∃ n, p n = 2183 + 30030 * d ∧ p (n + 1) = 2201 + 30030 * d ∧
      ∀ m ∈ Set.Ioo (p n) (p (n + 1)), m.minFac < p (n + 1) - p n := by
  have key : ∀ m, 2183 + 30030 * d < m → m < 2201 + 30030 * d →
      ∃ q, q.Prime ∧ q ≤ 13 ∧ q ∣ m := by
    intro m hm1 hm2
    obtain ⟨k, rfl⟩ : ∃ k, m = 2183 + 30030 * d + k := ⟨m - (2183 + 30030 * d), by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hk2 : k ≤ 17 := by omega
    interval_cases k
    all_goals first
      | exact ⟨2, Nat.prime_two, by norm_num, by omega⟩
      | exact ⟨3, Nat.prime_three, by norm_num, by omega⟩
      | exact ⟨5, Nat.prime_five, by norm_num, by omega⟩
      | exact ⟨7, by norm_num, by norm_num, by omega⟩
      | exact ⟨11, by norm_num, by norm_num, by omega⟩
      | exact ⟨13, by norm_num, by norm_num, by omega⟩
  have hnp : ∀ m, 2183 + 30030 * d < m → m < 2201 + 30030 * d → ¬ m.Prime := by
    intro m h1 h2 hm
    obtain ⟨q, hq, hq13, hqm⟩ := key m h1 h2
    have := (Nat.prime_dvd_prime_iff_eq hq hm).1 hqm
    omega
  have hcount : Nat.count Nat.Prime (2201 + 30030 * d) =
      Nat.count Nat.Prime (2183 + 30030 * d) + 1 := by
    have e : 2201 + 30030 * d = (2183 + 30030 * d + 1) + 17 := by ring
    rw [e, Nat.count_add, Nat.count_succ (p := Nat.Prime) (n := 2183 + 30030 * d), if_pos h₁]
    have h0 : Nat.count (fun k => Nat.Prime (2183 + 30030 * d + 1 + k)) 17 = 0 := by
      rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      rw [Finset.mem_range] at hx
      exact hnp _ (by omega) (by omega)
    omega
  have hp1 : p (Nat.count Nat.Prime (2183 + 30030 * d)) = 2183 + 30030 * d := Nat.nth_count h₁
  have hp2 : p (Nat.count Nat.Prime (2183 + 30030 * d) + 1) = 2201 + 30030 * d := by
    rw [← hcount]; exact Nat.nth_count h₂
  refine ⟨Nat.count Nat.Prime (2183 + 30030 * d), hp1, hp2, ?_⟩
  intro m hm
  rw [hp1, hp2] at hm ⊢
  obtain ⟨q, hq, hq13, hqm⟩ := key m hm.1 hm.2
  have := (Nat.minFac_le_of_dvd hq.two_le hqm).trans hq13
  omega

end OpenProofs.Erdos682
