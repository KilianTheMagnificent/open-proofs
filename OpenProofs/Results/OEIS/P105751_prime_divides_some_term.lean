import FormalConjectures.OEIS.«105751»

/-!
# `OeisA105751.prime_divides_some_term`

Upstream: `OeisA105751.prime_divides_some_term` (category textbook), `FormalConjectures/OEIS/105751.lean` line 72.
Proof idea: work with `P n = ∏_{k=0}^n (1 + k i)` in the Gaussian integers, so `a n = (P n).im`.
If `p ∣ n`, reflecting `k ↦ n - k` shows `P n ≡ conj (P n) (mod p)`, hence `p ∣ 2 (P n).im`, so
`p ∣ a n` for odd `p`. Modulo 3, three consecutive factors starting at `k ≡ 2` multiply to `-1`,
so `P (3m+1) ≡ ±(1 + i) (mod 3)` and `a (3m+1) ≢ 0 (mod 3)`, in particular `a (3m+1) ≠ 0`.
For a prime `p ≥ 5` take `n = p²` (`p² ≡ 1 mod 3`); for `p = 2, 3` use `a 4 = -40`, `a 2 = 3`.
-/

open Complex Filter Topology Nat
open OeisA105751

namespace OpenProofs.OeisA105751

/-- The product `∏_{k=0}^n (1 + k i)` in the Gaussian integers. -/
def a105751GProd (n : ℕ) : GaussianInt :=
  ∏ k ∈ Finset.range (n + 1), (1 + (k : GaussianInt) * ⟨0, 1⟩)

lemma a105751_a_eq_im (n : ℕ) : a n = (a105751GProd n).im := by
  have h : GaussianInt.toComplex (a105751GProd n) =
      ∏ k ∈ Finset.range (n + 1), (1 + (k : ℂ) * I) := by
    unfold a105751GProd
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro k _
    simp [GaussianInt.toComplex_def']
  unfold a
  simp only
  rw [← h, ← GaussianInt.intCast_im, Int.floor_intCast]

lemma a105751_star_factor (k : ℕ) :
    star (1 + (k : GaussianInt) * ⟨0, 1⟩) = 1 - (k : GaussianInt) * ⟨0, 1⟩ := by
  ext <;> simp

lemma a105751_dvd_im (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (hn : p ∣ n) :
    (p : ℤ) ∣ (a105751GProd n).im := by
  let π := Ideal.Quotient.mk (Ideal.span {((p : ℤ) : GaussianInt)})
  have hpn : π (n : GaussianInt) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    obtain ⟨c, rfl⟩ := hn
    exact ⟨c, by push_cast; ring⟩
  have hs : star (a105751GProd n) =
      ∏ k ∈ Finset.range (n + 1), (1 - (k : GaussianInt) * ⟨0, 1⟩) := by
    unfold a105751GProd
    rw [star_prod]
    simp only [a105751_star_factor]
  have key : π (a105751GProd n) = π (star (a105751GProd n)) := by
    rw [hs, map_prod]
    unfold a105751GProd
    rw [map_prod, ← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : j ≤ n := by simp at hj; omega
    have : n + 1 - 1 - j = n - j := by omega
    rw [this, Nat.cast_sub hj', map_add, map_mul, map_sub, hpn, map_sub, map_mul]
    ring
  have hdvd : ((p : ℤ) : GaussianInt) ∣ a105751GProd n - star (a105751GProd n) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
    exact key
  rw [Zsqrtd.intCast_dvd] at hdvd
  have h2 : (p : ℤ) ∣ 2 * (a105751GProd n).im := by
    have := hdvd.2
    simp only [Zsqrtd.im_sub, Zsqrtd.im_star] at this
    convert this using 1
    ring
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd h2 with h | h
  · exfalso
    have : p ∣ 2 := by exact_mod_cast h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 this
  · exact h

lemma a105751_mod_three (m : ℕ) :
    (3 : ℤ) ∣ (a105751GProd (3 * m + 1)).im - (-1) ^ m := by
  let π := Ideal.Quotient.mk (Ideal.span {((3 : ℤ) : GaussianInt)})
  have h3 : (3 : GaussianInt ⧸ Ideal.span {((3 : ℤ) : GaussianInt)}) = 0 := by
    have : π ((3 : ℤ) : GaussianInt) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    rw [map_intCast] at this
    exact_mod_cast this
  have hi : π ⟨0, 1⟩ ^ 2 = -1 := by
    rw [← map_pow, ← map_one π, ← map_neg]
    congr 1
  have key : ∀ m : ℕ, π (a105751GProd (3 * m + 1)) = (-1) ^ m * π (1 + ⟨0, 1⟩) := by
    intro m
    induction m with
    | zero =>
      simp [a105751GProd, Finset.prod_range_succ, show (⟨0, 0⟩ : GaussianInt) = 0 from rfl]
    | succ m ih =>
      have e : 3 * (m + 1) + 1 = 3 * m + 1 + 1 + 1 + 1 := by ring
      rw [e]
      unfold a105751GProd at ih ⊢
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        map_mul, map_mul, map_mul, ih]
      simp only [map_add, map_mul, map_one, map_natCast]
      push_cast
      set ι := π ⟨0, 1⟩
      linear_combination ((-1) ^ m * (1 + ι)) *
        (((-8 - 9 * (m : _ ) ^ 2 - 18 * m) + ((3 * m + 3) - (m + 1) * (3 * m + 2) * (3 * m + 4)) * ι)
          * h3 +
        (((3 * m + 2) * (3 * m + 3) + (3 * m + 3) * (3 * m + 4) + (3 * m + 4) * (3 * m + 2))
          + (3 * m + 2) * (3 * m + 3) * (3 * m + 4) * ι) * hi)
  have hdvd : ((3 : ℤ) : GaussianInt) ∣
      a105751GProd (3 * m + 1) - (((-1 : ℤ) ^ m : ℤ) : GaussianInt) * (1 + ⟨0, 1⟩) := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, key m, map_mul, map_intCast]
    push_cast
    rfl
  rw [Zsqrtd.intCast_dvd] at hdvd
  have := hdvd.2
  simp only [Zsqrtd.im_sub, Zsqrtd.im_smul, Zsqrtd.im_add, Zsqrtd.im_one] at this
  simpa using this

theorem prime_divides_some_term (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, a n ≠ 0 ∧ (p : ℤ) ∣ a n := by
  by_cases h2 : p = 2
  · subst h2
    exact ⟨4, by rw [a_4]; norm_num, by rw [a_4]; norm_num⟩
  by_cases h3 : p = 3
  · subst h3
    exact ⟨2, by rw [a_2]; norm_num, by rw [a_2]; norm_num⟩
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have : p % 3 ≠ 0 := by
      intro h
      have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this).symm
    omega
  have hmod : p * p % 3 = 1 := by
    rcases hp3 with h | h <;> simp [Nat.mul_mod, h]
  refine ⟨p * p, ?_, ?_⟩
  · rw [a105751_a_eq_im]
    intro h0
    have e : p * p = 3 * (p * p / 3) + 1 := by omega
    have h := a105751_mod_three (p * p / 3)
    rw [← e, h0, zero_sub, dvd_neg] at h
    have hu : IsUnit ((-1 : ℤ) ^ (p * p / 3)) := IsUnit.pow _ isUnit_neg_one
    have h3u := isUnit_of_dvd_unit h hu
    norm_num [Int.isUnit_iff] at h3u
  · rw [a105751_a_eq_im]
    exact a105751_dvd_im p hp h2 _ (dvd_mul_right p p)

end OpenProofs.OeisA105751
