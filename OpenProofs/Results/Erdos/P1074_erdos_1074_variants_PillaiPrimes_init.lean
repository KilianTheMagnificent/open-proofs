import FormalConjectures.ErdosProblems.«1074»

/-!
# `Erdos1074.erdos_1074.variants.PillaiPrimes_init`

Upstream: `Erdos1074.erdos_1074.variants.PillaiPrimes_init` (category test), `FormalConjectures/ErdosProblems/1074.lean` line 126.
Proof idea: a prime `p` divides `m!` for `m ≥ p`, so only `m < p` can witness membership in
`PillaiPrimes`; that makes membership of each `n ≤ 71` a bounded check, decided by the kernel
(primality of members by `norm_num`). Then compute `count` by `count_succ` and use `nth_count`.
-/

open scoped Nat
open Nat
open Erdos1074

namespace OpenProofs.Erdos1074

theorem pillai1074_mem_iff (n : ℕ) : n ∈ PillaiPrimes ↔
    n.Prime ∧ ∃ m < n, 1 ≤ m ∧ ¬ n ≡ 1 [MOD m] ∧ n ∣ m ! + 1 := by
  constructor
  · rintro ⟨hp, m, hm, hmod, hdvd⟩
    refine ⟨hp, m, ?_, hm, hmod, hdvd⟩
    by_contra! h
    have h1 : n ∣ m ! := Nat.dvd_factorial hp.pos h
    have h2 : n ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  · rintro ⟨hp, m, -, hm, hmod, hdvd⟩
    exact ⟨hp, m, hm, hmod, hdvd⟩

theorem pillai1074_nth_of_small (p : ℕ → Prop)
    (h : ∀ n, n ≤ 71 → (p n ↔ n ∈ [23, 29, 59, 61, 67, 71])) :
    nth p '' Set.Icc 0 5 = {23, 29, 59, 61, 67, 71} := by
  classical
  have hcount : ∀ n, n ≤ 71 → count p n =
      ((List.range n).filter (fun k => k ∈ [23, 29, 59, 61, 67, 71])).length := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.count_succ, ih (by omega), List.range_succ, List.filter_append,
        List.length_append]
      congr 1
      simp only [h n (by omega)]
      have hn' : n ≤ 70 := by omega
      interval_cases n <;> simp
  have hmem : ∀ n, n ∈ [23, 29, 59, 61, 67, 71] → p n := fun n hn =>
    (h n (by simp at hn; omega)).mpr hn
  have e0 : nth p 0 = 23 := by
    have := nth_count (hmem 23 (by simp)); rwa [hcount 23 (by norm_num)] at this
  have e1 : nth p 1 = 29 := by
    have := nth_count (hmem 29 (by simp)); rwa [hcount 29 (by norm_num)] at this
  have e2 : nth p 2 = 59 := by
    have := nth_count (hmem 59 (by simp)); rwa [hcount 59 (by norm_num)] at this
  have e3 : nth p 3 = 61 := by
    have := nth_count (hmem 61 (by simp)); rwa [hcount 61 (by norm_num)] at this
  have e4 : nth p 4 = 67 := by
    have := nth_count (hmem 67 (by simp)); rwa [hcount 67 (by norm_num)] at this
  have e5 : nth p 5 = 71 := by
    have := nth_count (hmem 71 (by simp)); rwa [hcount 71 (by norm_num)] at this
  have hI : Set.Icc (0 : ℕ) 5 = {0, 1, 2, 3, 4, 5} := by
    ext x; simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]; omega
  rw [hI]
  simp only [Set.image_insert_eq, Set.image_singleton, e0, e1, e2, e3, e4, e5]

theorem erdos_1074.variants.PillaiPrimes_init :
    nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  refine pillai1074_nth_of_small (fun n => n ∈ PillaiPrimes) ?_
  intro n hn
  simp only [pillai1074_mem_iff]
  interval_cases n <;>
    first
    | exact iff_of_true ⟨by norm_num, by decide +kernel⟩ (by decide)
    | (refine iff_of_false ?_ (by decide)
       rintro ⟨-, h2⟩
       revert h2
       decide +kernel)

end OpenProofs.Erdos1074
