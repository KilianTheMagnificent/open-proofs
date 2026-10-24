import FormalConjectures.ErdosProblems.«770»

/-!
# `Erdos770.erdos_770.variants.odd_h_unbounded`

Upstream: `Erdos770.erdos_770.variants.odd_h_unbounded` (category textbook), `FormalConjectures/ErdosProblems/770.lean` line 51.
Proof idea: given a bound `a`, Dirichlet's theorem gives a prime `q > 8 * a!` with
`q ≡ -1 (mod 8 * a!)`. Then `q ≡ 7 (mod 8)` and `q ≡ -1 (mod p)` for every odd prime `p ≤ a`,
so by quadratic reciprocity every prime `p ≤ a` (hence every `1 ≤ i ≤ a`) is a square mod `q`.
By Euler's criterion `q ∣ i ^ n - 1` for `n = q / 2`, which is odd since `q ≡ 3 (mod 4)`. So no
`m ≤ a` lies in the set defining `h n`, while `m = 2 ^ n` does (a common divisor `g ≥ 2` of all
`i ^ n - 1`, `2 ≤ i ≤ 2 ^ n`, would divide `g ^ n - 1` and `g ^ n`). Hence `a < h n < ⊤`.
-/

open Set ENat Filter
open Erdos770

namespace OpenProofs.Erdos770

/-- The gcd of `i ^ n - 1` over `2 ≤ i ≤ 2 ^ n` is `1`. -/
theorem erdos770_odd_gcd_pow_two (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc 2 (2 ^ n)).image fun i => (i ^ n - 1)).gcd id = 1 := by
  set g := ((Finset.Icc 2 (2 ^ n)).image fun i => (i ^ n - 1)).gcd id with hg
  have hdvd : ∀ i ∈ Finset.Icc 2 (2 ^ n), g ∣ i ^ n - 1 := fun i hi =>
    Finset.gcd_dvd (Finset.mem_image_of_mem _ hi)
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 := hdvd 2 (Finset.mem_Icc.mpr ⟨le_rfl, h2n⟩)
  have hpos : 0 < 2 ^ n - 1 := by omega
  have hgpos : 0 < g := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_dvd_iff] at h2; omega)
  have hgle : g ≤ 2 ^ n - 1 := Nat.le_of_dvd hpos h2
  by_contra hne
  have hg2 : 2 ≤ g := by omega
  have hgg := hdvd g (Finset.mem_Icc.mpr ⟨hg2, by omega⟩)
  have hgn : g ∣ g ^ n := dvd_pow_self g (by omega)
  have h1 : g ^ n - (g ^ n - 1) = 1 := by
    have : 1 ≤ g ^ n := Nat.one_le_pow _ _ hgpos
    omega
  have hd := Nat.dvd_sub hgn hgg
  rw [h1] at hd
  exact hne (Nat.dvd_one.mp hd)

/-- If `8 * k! ∣ q + 1` for a prime `q > k`, every `i ≤ k` is a square mod `q`. -/
theorem erdos770_odd_isSquare (k q : ℕ) [Fact q.Prime] (hkq : k < q)
    (hdvd : 8 * k.factorial ∣ q + 1) :
    ∀ i, i ≤ k → IsSquare (i : ZMod q) := by
  have hq8 : 8 ∣ q + 1 := dvd_trans (dvd_mul_right 8 _) hdvd
  have hq2 : q ≠ 2 := by omega
  have hq4 : q % 4 = 3 := by omega
  have hprime : ∀ p, p.Prime → p ≤ k → IsSquare (p : ZMod q) := by
    intro p hp hpk
    have := Fact.mk hp
    have hpq : p ≠ q := by omega
    have hpdvd : p ∣ q + 1 :=
      dvd_trans (Nat.dvd_factorial hp.pos hpk) (dvd_trans (dvd_mul_left _ 8) hdvd)
    have hqp : (q : ZMod p) = -1 := by
      have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    rcases hp.eq_two_or_odd' with rfl | hodd
    · have h2 := (ZMod.exists_sq_eq_two_iff hq2).mpr (Or.inr (by omega))
      simpa using h2
    · have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hodd with ⟨t, rfl⟩; omega
      rcases hp4 with h1 | h3
      · rw [← ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h1 hq2, hqp]
        exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
      · have hr := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h3 hq4 hpq
        rw [hqp] at hr
        have hn1 : ¬ IsSquare (-1 : ZMod p) := by
          rw [ZMod.exists_sq_eq_neg_one_iff]; omega
        by_contra hc
        exact hn1 (hr.mpr hc)
  intro i
  induction i using Nat.recOnMul with
  | zero => intro _; simp
  | one => intro _; simp
  | prime p hp => exact fun hpk => hprime p hp hpk
  | mul a b iha ihb =>
    intro hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    have hsa := iha (le_trans (Nat.le_mul_of_pos_right a hb) hab)
    have hsb := ihb (le_trans (Nat.le_mul_of_pos_left b ha) hab)
    push_cast
    exact hsa.mul hsb

theorem erdos_770.variants.odd_h_unbounded : Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd)) := by
  intro a
  have : NeZero (8 * a.factorial) := ⟨by have := Nat.factorial_pos a; omega⟩
  obtain ⟨q, hqgt, hqp, hqmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (q := 8 * a.factorial) (a := -1) isUnit_one.neg (8 * a.factorial)
  have := Fact.mk hqp
  have hM : 8 * a.factorial ∣ q + 1 := by
    have h0 : ((q + 1 : ℕ) : ZMod (8 * a.factorial)) = 0 := by
      push_cast; rw [hqmod]; ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hfac : a ≤ a.factorial := Nat.self_le_factorial a
  have hkq : a < q := by omega
  have hq4 : q % 4 = 3 := by
    have : 8 ∣ q + 1 := dvd_trans (dvd_mul_right 8 _) hM
    omega
  have hq8 : 8 ≤ q := by
    have := Nat.factorial_pos a
    omega
  set n := q / 2 with hn
  have hodd : Odd n := ⟨q / 4, by omega⟩
  have hsq := erdos770_odd_isSquare a q hkq hM
  have hdiv : ∀ i, 1 ≤ i → i ≤ a → q ∣ i ^ n - 1 := by
    intro i hi1 hia
    have hne : (i : ZMod q) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
    have he := (ZMod.euler_criterion q hne).mp (hsq i hia)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    rw [he, sub_self]
  refine ⟨(h n).toNat, ⟨h n, ⟨n, hodd, rfl⟩, rfl⟩, ?_⟩
  have hmem : ((2 ^ n : ℕ) : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1} := by
    refine ⟨?_, ?_⟩
    · have h4 : 2 < 2 ^ n := by
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast h4
    · rw [ENat.toNat_natCast]; exact erdos770_odd_gcd_pow_two n (by omega)
  have hlow : ∀ m ∈ {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1},
      ((a + 1 : ℕ) : ℕ∞) ≤ m := by
    rintro m ⟨-, hgcd⟩
    induction m using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      rw [ENat.toNat_natCast] at hgcd
      by_contra hlt
      have hma : m ≤ a := by
        have : (m : ℕ∞) < ((a + 1 : ℕ) : ℕ∞) := not_le.mp hlt
        have : m < a + 1 := by exact_mod_cast this
        omega
      have hq : q ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id := by
        rw [Finset.dvd_gcd_iff]
        intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        rw [Finset.mem_Icc] at hi
        exact hdiv i (by omega) (by omega)
      rw [hgcd] at hq
      exact hqp.one_lt.ne' (Nat.dvd_one.mp hq)
  have hle : h n ≤ ((2 ^ n : ℕ) : ℕ∞) := sInf_le hmem
  have hge : ((a + 1 : ℕ) : ℕ∞) ≤ h n := le_sInf hlow
  have hfin : h n ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← ht, ENat.toNat_natCast]
  rw [← ht] at hge
  have : a + 1 ≤ t := by exact_mod_cast hge
  omega

end OpenProofs.Erdos770
