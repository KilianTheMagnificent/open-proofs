import FormalConjectures.ErdosProblems.«770»

/-!
# `Erdos770.Nat.Prime.h_eq_add_one`

Upstream: `Erdos770.Nat.Prime.h_eq_add_one` (category textbook), `FormalConjectures/ErdosProblems/770.lean` line 45.
Proof idea: a prime `q` divides `gcd_{2 ≤ i ≤ m} (i ^ n - 1)` iff every `i ∈ [2, m]` is an `n`-th
root of unity mod `q`; then `q > m` (take `i = q`). If `q > n + 1`, the residues `1, …, n` and
`2b` with `b = (n + 2) / 2` (so `n < 2b < q`) are `n + 1` distinct `n`-th roots of unity in
`ZMod q`, contradicting the bound `n` on the number of roots of `X ^ n - 1`. Hence the gcd is `1`
for `m ≥ n + 1`, and for `m = n` unless `q = n + 1` is prime. If `n + 1 = p` is prime, Fermat
gives `p ∣ i ^ n - 1` for all `i ∈ [2, n]`, so no `m ≤ n` qualifies.
-/

open Set ENat Filter
open Erdos770

namespace OpenProofs.Erdos770

/-- For a prime `q > n + 1`, the residues `1, …, n` are not all `n`-th roots of unity mod `q`. -/
theorem erdos770_roots_key {n q : ℕ} (hq : q.Prime) (hn : 2 ≤ n) (hqn : n + 1 < q)
    (h : ∀ i ∈ Finset.Icc 1 n, ((i : ZMod q)) ^ n = 1) : False := by
  have := Fact.mk hq
  set b := (n + 2) / 2 with hb
  have hbn : b ≤ n := by omega
  have h2b : n < 2 * b := by omega
  have h2bq : 2 * b < q := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h2 : 2 * b = n + 2 := by omega
      rw [h2]
      rcases (show n + 2 < q ∨ n + 2 = q by omega) with h' | h'
      · exact h'
      · exfalso
        have := hq.eq_one_or_self_of_dvd 2 ⟨k + 1, by omega⟩
        omega
    · omega
  let T : Finset ℕ := insert (2 * b) (Finset.Icc 1 n)
  have hTcard : T.card = n + 1 := by
    rw [Finset.card_insert_of_notMem (by simp; omega)]
    simp
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod q)) T := by
    intro x hx y hy hxy
    have hx' : x < q := by
      simp only [T, Finset.coe_insert, Finset.coe_Icc, Set.mem_insert_iff, Set.mem_Icc] at hx
      omega
    have hy' : y < q := by
      simp only [T, Finset.coe_insert, Finset.coe_Icc, Set.mem_insert_iff, Set.mem_Icc] at hy
      omega
    have := congrArg ZMod.val hxy
    simpa [ZMod.val_cast_of_lt hx', ZMod.val_cast_of_lt hy'] using this
  have hsub : T.image (fun x : ℕ => (x : ZMod q)) ⊆
      Polynomial.nthRootsFinset n (1 : ZMod q) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [Polynomial.mem_nthRootsFinset (by omega)]
    simp only [T, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [Nat.cast_mul, mul_pow, h 2 (by simp; omega), h b (by simp; omega), one_mul]
    · exact h x hx
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, hTcard] at hle
  have hroots : (Polynomial.nthRootsFinset n (1 : ZMod q)).card ≤ n := by
    classical
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  omega

theorem erdos770_dvd_iff {q i n : ℕ} (hi : 1 ≤ i) :
    q ∣ i ^ n - 1 ↔ ((i : ZMod q)) ^ n = 1 := by
  have h1 : 1 ≤ i ^ n := Nat.one_le_pow _ _ hi
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  push_cast
  exact sub_eq_zero

theorem erdos770_dvd_gcd_iff {q m n : ℕ} :
    q ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id ↔
      ∀ i ∈ Finset.Icc 2 m, ((i : ZMod q)) ^ n = 1 := by
  rw [Finset.dvd_gcd_iff]
  simp only [Finset.mem_image, id, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun i hi => ?_
  exact erdos770_dvd_iff (by simp at hi; omega)

/-- A prime with every `i ∈ [2, m]` an `n`-th root of unity mod `q` exceeds `m`. -/
theorem erdos770_lt_of_roots {q m n : ℕ} (hq : q.Prime) (hn : 1 ≤ n)
    (h : ∀ i ∈ Finset.Icc 2 m, ((i : ZMod q)) ^ n = 1) : m < q := by
  by_contra hc
  have := Fact.mk hq
  have := h q (by simp; exact ⟨hq.two_le, by omega⟩)
  rw [ZMod.natCast_self, zero_pow (by omega)] at this
  exact zero_ne_one this

/-- For `m ≥ n` and a prime `q` with all `i ∈ [2, m]` `n`-th roots of unity mod `q`, `q = n + 1`. -/
theorem erdos770_eq_of_roots {q m n : ℕ} (hq : q.Prime) (hn : 2 ≤ n) (hm : n ≤ m)
    (h : ∀ i ∈ Finset.Icc 2 m, ((i : ZMod q)) ^ n = 1) : q = n + 1 := by
  have hlt := erdos770_lt_of_roots hq (by omega) h
  by_contra hne
  refine erdos770_roots_key hq hn (by omega) fun i hi => ?_
  rcases (show i = 1 ∨ 2 ≤ i by simp at hi; omega) with rfl | hi2
  · simp
  · exact h i (by simp at hi ⊢; omega)

theorem Nat.Prime.h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := by
  constructor
  · intro hh
    by_contra hnp
    have hmem : ((n : ℕ) : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
        ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1} := by
      refine ⟨by exact_mod_cast hn, ?_⟩
      rw [ENat.toNat_natCast, Nat.eq_one_iff_not_exists_prime_dvd]
      intro q hq hdvd
      rw [erdos770_dvd_gcd_iff] at hdvd
      have := erdos770_eq_of_roots hq (by omega) le_rfl hdvd
      exact hnp (this ▸ hq)
    have hle : h n ≤ (n : ℕ∞) := sInf_le hmem
    rw [hh] at hle
    have : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hle
    have := ENat.natCast_le_natCast.mp this
    omega
  · intro hp
    have := Fact.mk hp
    apply le_antisymm
    · apply sInf_le
      refine ⟨by exact_mod_cast (show 2 < n + 1 by omega), ?_⟩
      have : ((n : ℕ∞) + 1).toNat = n + 1 := by exact_mod_cast ENat.toNat_natCast (n + 1)
      rw [this, Nat.eq_one_iff_not_exists_prime_dvd]
      intro q hq hdvd
      rw [erdos770_dvd_gcd_iff] at hdvd
      have h1 := erdos770_eq_of_roots hq (by omega) (by omega) hdvd
      have h2 := erdos770_lt_of_roots hq (by omega) hdvd
      omega
    · refine le_sInf fun m hm => ?_
      obtain ⟨hm2, hmg⟩ := hm
      induction m using ENat.recTopCoe with
      | top => exact le_top
      | coe k =>
        rw [ENat.toNat_natCast] at hmg
        have hk2 : 2 < k := by exact_mod_cast hm2
        by_contra hlt
        have hkn : k ≤ n := by
          have : (k : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by push_cast; exact lt_of_not_ge hlt
          have := ENat.natCast_lt_natCast.mp this
          omega
        have hdvd : (n + 1) ∣ ((Finset.Icc 2 k).image fun i => (i ^ n - 1)).gcd id := by
          rw [erdos770_dvd_gcd_iff]
          intro i hi
          simp only [Finset.mem_Icc] at hi
          have hne : ((i : ZMod (n + 1))) ≠ 0 := by
            rw [Ne, ZMod.natCast_eq_zero_iff]
            intro hd
            have := Nat.le_of_dvd (by omega) hd
            omega
          have := ZMod.pow_card_sub_one_eq_one hne
          simpa using this
        rw [hmg] at hdvd
        have := Nat.le_of_dvd one_pos hdvd
        omega

end OpenProofs.Erdos770
