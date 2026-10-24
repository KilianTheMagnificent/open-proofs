import FormalConjectures.ErdosProblems.«1074»

/-!
# `Erdos1074.erdos_1074.variants.EHSNumbers_init`

Upstream: `Erdos1074.erdos_1074.variants.EHSNumbers_init` (category test), `FormalConjectures/ErdosProblems/1074.lean` line 120.
Proof idea: decide membership of each `m ≤ 17` in `EHSNumbers` (witness primes for members,
full prime factorizations of `m! + 1` for non-members), compute `count` by `count_succ`, and
use `nth_count`.
-/

open scoped Nat
open Nat
open Erdos1074

namespace OpenProofs.Erdos1074

theorem ehs1074_not_mem_of_factors {m : ℕ} (l : List ℕ)
    (hl : ∀ q ∈ l, q.Prime ∧ q ≡ 1 [MOD m]) (hN : m ! + 1 = l.prod) : m ∉ EHSNumbers := by
  rintro ⟨_, p, hp, hmod, hdvd⟩
  rw [hN] at hdvd
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_prod_iff hp.prime).mp hdvd
  obtain ⟨hqp, hq1⟩ := hl q hq
  rw [(Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq] at hmod
  exact hmod hq1

theorem ehs1074_mem_of_witness {m : ℕ} (p : ℕ) (hm : 1 ≤ m) (hp : p.Prime)
    (hmod : ¬ p ≡ 1 [MOD m]) (hdvd : p ∣ m ! + 1) : m ∈ EHSNumbers :=
  ⟨hm, p, hp, hmod, hdvd⟩

theorem ehs1074_not0 : 0 ∉ EHSNumbers := fun h => by simp at h
theorem ehs1074_not1 : 1 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [2] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not2 : 2 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [3] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not3 : 3 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [7] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not4 : 4 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [5, 5] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not5 : 5 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [11, 11] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not6 : 6 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [7, 103] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not7 : 7 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [71, 71] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not10 : 10 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [11, 329891] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not11 : 11 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [39916801] (by norm_num [Nat.ModEq]) (by decide)
theorem ehs1074_not12 : 12 ∉ EHSNumbers :=
  ehs1074_not_mem_of_factors [13, 13, 2834329] (by norm_num [Nat.ModEq]) (by decide)

theorem ehs1074_mem8 : 8 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 61 (by norm_num) (by norm_num) (by decide) (by decide)
theorem ehs1074_mem9 : 9 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 71 (by norm_num) (by norm_num) (by decide) (by decide)
theorem ehs1074_mem13 : 13 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 83 (by norm_num) (by norm_num) (by decide) (by decide)
theorem ehs1074_mem14 : 14 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 23 (by norm_num) (by norm_num) (by decide) (by decide)
theorem ehs1074_mem15 : 15 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 59 (by norm_num) (by norm_num) (by decide) (by decide)
theorem ehs1074_mem16 : 16 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 61 (by norm_num) (by norm_num) (by decide) (by decide)
theorem ehs1074_mem17 : 17 ∈ EHSNumbers :=
  ehs1074_mem_of_witness 661 (by norm_num) (by norm_num) (by decide) (by decide)

theorem ehs1074_nth_of_small (p : ℕ → Prop)
    (h : ∀ n, n ≤ 17 → (p n ↔ n ∈ [8, 9, 13, 14, 15, 16, 17])) :
    nth p '' Set.Icc 0 6 = {8, 9, 13, 14, 15, 16, 17} := by
  classical
  have hcount : ∀ n, n ≤ 17 → count p n =
      ((List.range n).filter (fun k => k ∈ [8, 9, 13, 14, 15, 16, 17])).length := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.count_succ, ih (by omega), List.range_succ, List.filter_append,
        List.length_append]
      congr 1
      simp only [h n (by omega)]
      have hn' : n ≤ 16 := by omega
      interval_cases n <;> simp
  have hmem : ∀ n, n ∈ [8, 9, 13, 14, 15, 16, 17] → p n := fun n hn =>
    (h n (by simp at hn; omega)).mpr hn
  have e0 : nth p 0 = 8 := by
    have := nth_count (hmem 8 (by simp)); rwa [hcount 8 (by norm_num)] at this
  have e1 : nth p 1 = 9 := by
    have := nth_count (hmem 9 (by simp)); rwa [hcount 9 (by norm_num)] at this
  have e2 : nth p 2 = 13 := by
    have := nth_count (hmem 13 (by simp)); rwa [hcount 13 (by norm_num)] at this
  have e3 : nth p 3 = 14 := by
    have := nth_count (hmem 14 (by simp)); rwa [hcount 14 (by norm_num)] at this
  have e4 : nth p 4 = 15 := by
    have := nth_count (hmem 15 (by simp)); rwa [hcount 15 (by norm_num)] at this
  have e5 : nth p 5 = 16 := by
    have := nth_count (hmem 16 (by simp)); rwa [hcount 16 (by norm_num)] at this
  have e6 : nth p 6 = 17 := by
    have := nth_count (hmem 17 (by simp)); rwa [hcount 17 (by norm_num)] at this
  have hI : Set.Icc (0 : ℕ) 6 = {0, 1, 2, 3, 4, 5, 6} := by
    ext x; simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  rw [hI]
  simp only [Set.image_insert_eq, Set.image_singleton, e0, e1, e2, e3, e4, e5, e6]

theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  refine ehs1074_nth_of_small (fun n => n ∈ EHSNumbers) ?_
  intro n hn
  have := ehs1074_not0; have := ehs1074_not1; have := ehs1074_not2; have := ehs1074_not3
  have := ehs1074_not4; have := ehs1074_not5; have := ehs1074_not6; have := ehs1074_not7
  have := ehs1074_not10; have := ehs1074_not11; have := ehs1074_not12
  have := ehs1074_mem8; have := ehs1074_mem9; have := ehs1074_mem13; have := ehs1074_mem14
  have := ehs1074_mem15; have := ehs1074_mem16; have := ehs1074_mem17
  interval_cases n <;>
    first
    | exact iff_of_true ‹_› (by decide)
    | exact iff_of_false ‹_› (by decide)

end OpenProofs.Erdos1074
