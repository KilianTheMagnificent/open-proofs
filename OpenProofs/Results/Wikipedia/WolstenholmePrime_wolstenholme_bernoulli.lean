import FormalConjectures.Wikipedia.WolstenholmePrime

/-!
# `WolstenholmePrime.wolstenholme_bernoulli`

Upstream: `WolstenholmePrime.wolstenholme_bernoulli` (category textbook), `FormalConjectures/Wikipedia/WolstenholmePrime.lean` line 71.
Proof idea: let `f(x) = ∏_{k=1}^{p-1} (x + k) = ∑ s_j x^j`. Then `f(p) = (p-1)! C(2p-1, p-1)`,
`f(0) = (p-1)!` and `f(-p) = f(0)`, so `f(p) + f(-p) - 2 f(0) ≡ 2 p² s_2 (mod p⁴)` gives
`C(2p-1, p-1) ≡ 1 (mod p⁴) ↔ p² ∣ s_2 = e_{p-3}(1, …, p-1)`. Newton's identities, together with
`p ∣ ∑_{k<p} k^j` and `p ∣ e_j(1, …, p-1)` for `1 ≤ j ≤ p - 2`, give
`(p - 3) e_{p-3} ≡ -∑_{k<p} k^{p-3} (mod p²)`. Finally Faulhaber's formula and the `p`-integrality
of `B_j` for `j < p - 1` (from the recurrence) give `∑_{k<p} k^{p-3} ≡ p B_{p-3} (mod p³)` in
`ℚ_[p]` (the `B_{p-4}` term vanishes), so `p² ∣ ∑_{k<p} k^{p-3} ↔ p ∣ num(B_{p-3})`.
-/

open WolstenholmePrime Finset

namespace OpenProofs.WolstenholmePrime

-- p-adic part: Faulhaber's formula modulo powers of `p`.

lemma wbern_natCast_norm_le_one (p : ℕ) [Fact p.Prime] (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  exact_mod_cast Padic.norm_int_le_one (p := p) (n : ℤ)

lemma wbern_natCast_norm_eq_one (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (h0 : 0 < n) (hn : n < p) :
    ‖(n : ℚ_[p])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (Nat.not_dvd_of_pos_of_lt h0 hn))

/-- Bernoulli numbers `B'_n` with `n + 1 < p` are `p`-integral. -/
lemma wbern_bernoulli'_norm_le_one (p : ℕ) [hp : Fact p.Prime] :
    ∀ n, n + 1 < p → ‖((bernoulli' n : ℚ) : ℚ_[p])‖ ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [bernoulli'_def, Rat.cast_sub, Rat.cast_one, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le (by simp) ?_)
    rw [norm_neg, Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
    intro k hk
    rw [Finset.mem_range] at hk
    have hk' : ((n : ℚ) - k + 1) = ((n - k + 1 : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub hk.le]; ring
    rw [hk', Rat.cast_mul, Rat.cast_div, norm_mul, norm_div, Rat.cast_natCast, Rat.cast_natCast,
      wbern_natCast_norm_eq_one p (n - k + 1) (by omega) (by omega), div_one]
    exact mul_le_one₀ (wbern_natCast_norm_le_one p _) (norm_nonneg _) (ih k hk (by omega))

lemma wbern_bernoulli_norm_le_one (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n + 1 < p) :
    ‖((bernoulli n : ℚ) : ℚ_[p])‖ ≤ 1 := by
  rw [_root_.bernoulli, Rat.cast_mul, norm_mul, Rat.cast_pow, norm_pow, Rat.cast_neg, Rat.cast_one,
    norm_neg, norm_one, one_pow, one_mul]
  exact wbern_bernoulli'_norm_le_one p n hn

/-- The `i`-th term of Faulhaber's formula for `∑_{k<p} k^m` has norm at most `p^{-(m+1-i)}`. -/
lemma wbern_term_norm (p : ℕ) [hp : Fact p.Prime] (m i : ℕ) (hm : m + 2 ≤ p) (hi : i ≤ m) :
    ‖(((bernoulli i * ((m + 1).choose i) * (p : ℚ) ^ (m + 1 - i) / (m + 1) : ℚ)) : ℚ_[p])‖
      ≤ (p : ℝ) ^ (-((m + 1 - i : ℕ) : ℤ)) := by
  have hm1 : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hm1, Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_natCast, Rat.cast_natCast, norm_div, norm_mul, norm_mul, Padic.norm_p_pow,
    wbern_natCast_norm_eq_one p (m + 1) (by omega) (by omega), div_one]
  refine mul_le_of_le_one_left (by positivity) ?_
  exact mul_le_one₀ (wbern_bernoulli_norm_le_one p i (by omega)) (norm_nonneg _)
    (wbern_natCast_norm_le_one p _)

lemma wbern_sum_cast (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (((∑ k ∈ range p, (k : ℤ) ^ m : ℤ)) : ℚ_[p]) =
      ((∑ i ∈ range (m + 1), bernoulli i * ((m + 1).choose i) * (p : ℚ) ^ (m + 1 - i) / (m + 1)
        : ℚ) : ℚ_[p]) := by
  rw [← sum_range_pow]
  push_cast
  rfl

/-- Power sums `∑_{k<p} k^j` with `1 ≤ j ≤ p - 2` are divisible by `p`. -/
lemma wbern_psum_dvd (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj : j + 2 ≤ p) :
    (p : ℤ) ∣ ∑ k ∈ range p, (k : ℤ) ^ j := by
  have h := (Padic.norm_int_le_pow_iff_dvd (p := p) (∑ k ∈ range p, (k : ℤ) ^ j) 1).mp ?_
  · simpa using h
  rw [wbern_sum_cast, Rat.cast_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro i hi
  rw [mem_range] at hi
  refine (wbern_term_norm p j i hj (by omega)).trans ?_
  apply zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le)
  omega

lemma wbern_rat_norm_le_iff (p : ℕ) [hp : Fact p.Prime] (q : ℚ) :
    ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) ↔ (p : ℤ) ∣ q.num := by
  have hq : (q : ℚ_[p]) = (q.num : ℚ_[p]) / (q.den : ℚ_[p]) := by
    rw [Rat.cast_def]
  have hden0 : (q.den : ℚ_[p]) ≠ 0 := by exact_mod_cast q.den_nz
  have key : ‖(q.num : ℚ_[p])‖ = ‖(q : ℚ_[p])‖ * ‖(q.den : ℚ_[p])‖ := by
    rw [hq, norm_div, div_mul_cancel₀]
    exact norm_ne_zero_iff.mpr hden0
  constructor
  · intro h
    have h2 : ‖((q.num : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [key]
      calc ‖(q : ℚ_[p])‖ * ‖(q.den : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ)) * 1 :=
            mul_le_mul h (wbern_natCast_norm_le_one p _) (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    simpa using (Padic.norm_int_le_pow_iff_dvd q.num 1).mp h2
  · intro h
    have hnd : ¬ p ∣ q.den := by
      intro hd
      have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp h
      have := Nat.dvd_gcd h1 hd
      rw [q.reduced.gcd_eq_one] at this
      exact hp.out.not_dvd_one this
    have h1 : ‖(q.den : ℚ_[p])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
    have h2 := (Padic.norm_int_le_pow_iff_dvd (p := p) q.num 1).mpr (by simpa using h)
    rw [key, h1, mul_one] at h2
    exact h2

/-- Step C: `p² ∣ ∑_{k<p} k^{p-3}` iff `p` divides the numerator of `B_{p-3}`. -/
lemma wbern_stepC (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 < p) :
    ((p : ℤ) ^ 2) ∣ (∑ k ∈ range p, (k : ℤ) ^ (p - 3)) ↔ (p : ℤ) ∣ (bernoulli' (p - 3)).num := by
  obtain ⟨n, hn⟩ : ∃ n, p - 3 = n + 2 := ⟨p - 5, by omega⟩
  have hodd : Odd (n + 1) := by
    rcases hp.out.eq_two_or_odd' with h | h
    · omega
    · obtain ⟨r, hr⟩ := h
      exact ⟨r - 2, by omega⟩
  set R : ℚ := ∑ i ∈ range (n + 1),
    bernoulli i * ((n + 2 + 1).choose i) * (p : ℚ) ^ (n + 2 + 1 - i) / ((n + 2 : ℕ) + 1) with hRdef
  have hsplitQ : (∑ i ∈ range (n + 2 + 1), bernoulli i * ((n + 2 + 1).choose i) *
      (p : ℚ) ^ (n + 2 + 1 - i) / ((n + 2 : ℕ) + 1)) = R + p * bernoulli' (n + 2) := by
    rw [sum_range_succ, sum_range_succ, bernoulli_eq_zero_of_odd hodd (by omega),
      bernoulli_eq_bernoulli'_of_ne_one (by omega : n + 2 ≠ 1), Nat.choose_succ_self_right,
      show n + 2 + 1 - (n + 2) = 1 by omega, hRdef]
    have h3 : ((n + 2 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hsplit : ((∑ k ∈ range p, (k : ℤ) ^ (p - 3) : ℤ) : ℚ_[p]) =
      (R : ℚ_[p]) + (p : ℚ_[p]) * ((bernoulli' (p - 3) : ℚ) : ℚ_[p]) := by
    rw [wbern_sum_cast, hn, hsplitQ]
    push_cast
    ring
  have hR : ‖(R : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
    rw [hRdef, Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro i hi
    rw [mem_range] at hi
    refine (wbern_term_norm p (n + 2) i (by omega) (by omega)).trans ?_
    apply zpow_le_zpow_right₀ (by exact_mod_cast hp.out.one_lt.le)
    omega
  rw [← wbern_rat_norm_le_iff, ← Padic.norm_int_le_pow_iff_dvd, hsplit]
  set t : ℝ := (p : ℝ)⁻¹ with ht
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  have e1 : (p : ℝ) ^ (-((1 : ℕ) : ℤ)) = t := by simp [ht]
  have e2 : (p : ℝ) ^ (-((2 : ℕ) : ℤ)) = t * t := by
    rw [zpow_neg, zpow_natCast, ht, ← inv_pow, pow_two]
  have e3 : (p : ℝ) ^ (-((3 : ℕ) : ℤ)) = t * t * t := by
    rw [zpow_neg, zpow_natCast, ht, ← inv_pow, pow_three, mul_assoc]
  rw [e1, e2]
  rw [e3] at hR
  have hR' : ‖(R : ℚ_[p])‖ ≤ t * t :=
    hR.trans (mul_le_of_le_one_right (by positivity) ht1)
  have hpB : ‖(p : ℚ_[p]) * ((bernoulli' (p - 3) : ℚ) : ℚ_[p])‖
      = t * ‖((bernoulli' (p - 3) : ℚ) : ℚ_[p])‖ := by
    rw [norm_mul, Padic.norm_p]
  constructor
  · intro h
    have h2 : ‖(p : ℚ_[p]) * ((bernoulli' (p - 3) : ℚ) : ℚ_[p])‖ ≤ t * t := by
      have := Padic.nonarchimedean ((R : ℚ_[p]) + (p : ℚ_[p]) * ((bernoulli' (p - 3) : ℚ) : ℚ_[p]))
        (-(R : ℚ_[p]))
      rw [norm_neg, add_neg_cancel_comm] at this
      exact this.trans (max_le h hR')
    rw [hpB] at h2
    exact le_of_mul_le_mul_left h2 ht0
  · intro h
    refine (Padic.nonarchimedean _ _).trans (max_le hR' ?_)
    rw [hpB]
    exact mul_le_mul_of_nonneg_left h ht0.le

-- Integer part: Newton's identities for the elementary symmetric functions of `1, …, p - 1`.

lemma wbern_newton (n : ℕ) (x : Fin n → ℤ) (k : ℕ) :
    (k : ℤ) * ∑ t ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ t, x i =
      (-1) ^ (k + 1) * ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (∑ t ∈ (univ : Finset (Fin n)).powersetCard a.1, ∏ i ∈ t, x i) *
          ∑ i, x i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℤ k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.esymm_map_val, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  exact h

lemma wbern_psum_fin (p j : ℕ) (hp : 1 ≤ p) (hj : 1 ≤ j) :
    ∑ i : Fin (p - 1), (((i : ℕ) : ℤ) + 1) ^ j = ∑ k ∈ range p, (k : ℤ) ^ j := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ((k : ℤ) + 1) ^ j) (p - 1)]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [sum_range_succ' (fun k => (k : ℤ) ^ j)]
  simp [zero_pow (by omega : j ≠ 0)]

lemma wbern_esymm_dvd (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj1 : 1 ≤ j) (hj : j + 2 ≤ p) :
    (p : ℤ) ∣ ∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard j, ∏ i ∈ t, (((i : ℕ) : ℤ) + 1) := by
  have hN := wbern_newton (p - 1) (fun i => ((i : ℕ) : ℤ) + 1) j
  have hdvd : (p : ℤ) ∣ (j : ℤ) *
      ∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard j, ∏ i ∈ t, (((i : ℕ) : ℤ) + 1) := by
    rw [hN]
    apply Dvd.dvd.mul_left
    apply Finset.dvd_sum
    intro a ha
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    apply Dvd.dvd.mul_left
    rw [wbern_psum_fin p a.2 hp.out.one_lt.le (by omega)]
    exact wbern_psum_dvd p a.2 (by omega)
  have hcop : IsCoprime (p : ℤ) (j : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- Step B: `(p - 3) e_{p-3}(1, …, p-1) + ∑_{k<p} k^{p-3} ≡ 0 (mod p²)`. -/
lemma wbern_stepB (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 < p) :
    ((p : ℤ) ^ 2) ∣ ((p - 3 : ℕ) : ℤ) *
        (∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard (p - 3), ∏ i ∈ t, (((i : ℕ) : ℤ) + 1)) +
      ∑ k ∈ range p, (k : ℤ) ^ (p - 3) := by
  have hN := wbern_newton (p - 1) (fun i => ((i : ℕ) : ℤ) + 1) (p - 3)
  have hmem : ((0 : ℕ), p - 3) ∈ (antidiagonal (p - 3)).filter (fun a => a.1 < p - 3) := by
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
    omega
  rw [← Finset.add_sum_erase _ _ hmem] at hN
  have hodd : (-1 : ℤ) ^ (p - 3 + 1) = -1 := by
    rcases hp.out.eq_two_or_odd' with h | h
    · omega
    · obtain ⟨r, hr⟩ := h
      rw [show p - 3 + 1 = 2 * (r - 1) + 1 by omega]
      simp [pow_succ, pow_mul]
  rw [hodd] at hN
  simp only [pow_zero, one_mul, powersetCard_zero, sum_singleton, prod_empty] at hN
  rw [wbern_psum_fin p (p - 3) hp.out.one_lt.le (by omega)] at hN
  rw [hN]
  have hrest : (p : ℤ) ^ 2 ∣ ∑ a ∈ ((antidiagonal (p - 3)).filter (fun a => a.1 < p - 3)).erase
      ((0 : ℕ), p - 3), (-1) ^ a.1 *
        (∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard a.1, ∏ i ∈ t, (((i : ℕ) : ℤ) + 1)) *
          ∑ i : Fin (p - 1), (((i : ℕ) : ℤ) + 1) ^ a.2 := by
    apply Finset.dvd_sum
    intro a ha
    rw [Finset.mem_erase, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    have ha1 : a.1 ≠ 0 := by
      intro h
      apply ha.1
      ext
      · simp [h]
      · simp only; omega
    rw [pow_two, mul_assoc]
    apply Dvd.dvd.mul_left
    apply mul_dvd_mul (wbern_esymm_dvd p a.1 (by omega) (by omega))
    rw [wbern_psum_fin p a.2 hp.out.one_lt.le (by omega)]
    exact wbern_psum_dvd p a.2 (by omega)
  obtain ⟨c, hc⟩ := hrest
  rw [hc]
  exact ⟨-c, by ring⟩

open Polynomial in
/-- Step A: `(p-1)! (C(2p-1, p-1) - 1) ≡ 2 p² e_{p-3}(1, …, p-1) (mod p⁴)`, from the symmetry
`f(-p) = f(0)` of `f(x) = ∏_{k=1}^{p-1} (x + k)`. -/
lemma wbern_stepA (p : ℕ) [hp : Fact p.Prime] (hp7 : 7 < p) :
    ((p : ℤ) ^ 4) ∣ ((p - 1).factorial : ℤ) * ((((2 * p - 1).choose (p - 1) : ℕ) : ℤ) - 1) -
      2 * (p : ℤ) ^ 2 *
        ∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard (p - 3), ∏ i ∈ t, (((i : ℕ) : ℤ) + 1) := by
  set f : ℤ[X] := ∏ i : Fin (p - 1), (X + C (((i : ℕ) : ℤ) + 1)) with hf
  have hcoeff : f.coeff 2 =
      ∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard (p - 3), ∏ i ∈ t, (((i : ℕ) : ℤ) + 1) := by
    rw [hf, Finset.prod_X_add_C_coeff _ _ (by simp; omega)]
    simp only [card_univ, Fintype.card_fin]
    rw [show p - 1 - 2 = p - 3 by omega]
  have hdeg : f.natDegree < p := by
    rw [hf]
    refine (natDegree_prod_le _ _).trans_lt ?_
    simp only [natDegree_X_add_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  have hevalF : ∀ y : ℤ, f.eval y = ∏ k ∈ range (p - 1), (y + ((k : ℤ) + 1)) := by
    intro y
    rw [hf, eval_prod]
    simp only [eval_add, eval_X, eval_C]
    exact Fin.prod_univ_eq_prod_range (fun k => y + ((k : ℤ) + 1)) (p - 1)
  have h0 : f.eval 0 = ((p - 1).factorial : ℤ) := by
    rw [hevalF, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    simp
  have hpos : f.eval (p : ℤ) = ((p - 1).factorial : ℤ) * ((2 * p - 1).choose (p - 1) : ℕ) := by
    rw [hevalF]
    have h1 := Nat.ascFactorial_eq_factorial_mul_choose p (p - 1)
    rw [Nat.ascFactorial_eq_prod_range, show p + (p - 1) = 2 * p - 1 by omega] at h1
    have h2 := congrArg (fun n : ℕ => (n : ℤ)) h1
    simp only [Nat.cast_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h2
    rw [← h2]
    apply prod_congr rfl
    intro k _
    ring
  have hneg : f.eval (-(p : ℤ)) = ((p - 1).factorial : ℤ) := by
    rw [← h0, hevalF, hevalF]
    rw [← Finset.prod_range_reflect (fun k => (0 : ℤ) + ((k : ℤ) + 1)) (p - 1)]
    have : ∀ k ∈ range (p - 1),
        -(p : ℤ) + ((k : ℤ) + 1) = -((0 : ℤ) + (((p - 1 - 1 - k : ℕ) : ℤ) + 1)) := by
      intro k hk
      rw [mem_range] at hk
      rw [show p - 1 - 1 - k = p - (k + 2) by omega, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [prod_congr rfl this, prod_neg, card_range]
    have hev : Even (p - 1) := by
      rcases hp.out.eq_two_or_odd' with h | h
      · omega
      · obtain ⟨r, hr⟩ := h
        exact ⟨r, by omega⟩
    rw [hev.neg_one_pow, one_mul]
  have key : (p : ℤ) ^ 4 ∣
      f.eval (p : ℤ) + f.eval (-(p : ℤ)) - 2 * f.coeff 0 - 2 * (p : ℤ) ^ 2 * f.coeff 2 := by
    rw [eval_eq_sum_range' hdeg, eval_eq_sum_range' hdeg, ← sum_add_distrib,
      ← Finset.sum_range_add_sum_Ico _ (by omega : 4 ≤ p)]
    have hI : ∀ i ∈ Ico 4 p,
        (p : ℤ) ^ 4 ∣ f.coeff i * (p : ℤ) ^ i + f.coeff i * (-(p : ℤ)) ^ i := by
      intro i hi
      rw [mem_Ico] at hi
      rw [← mul_add]
      apply Dvd.dvd.mul_left
      apply dvd_add (pow_dvd_pow _ hi.1)
      exact (pow_dvd_pow_of_dvd (dvd_neg.mpr dvd_rfl) 4).trans (pow_dvd_pow _ hi.1)
    obtain ⟨c, hc⟩ := Finset.dvd_sum hI
    rw [hc]
    simp only [sum_range_succ, sum_range_zero]
    exact ⟨c, by ring⟩
  rw [← hcoeff]
  have hc0 : f.coeff 0 = ((p - 1).factorial : ℤ) := by rw [coeff_zero_eq_eval_zero, h0]
  rw [hpos, hneg, hc0] at key
  obtain ⟨c, hc⟩ := key
  exact ⟨c, by linear_combination hc⟩

lemma wbern_main (p : ℕ) (hp : p.Prime) (hp7 : 7 < p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4] ↔ (p : ℤ) ∣ (bernoulli' (p - 3)).num := by
  have := Fact.mk hp
  have hA := wbern_stepA p hp7
  have hB := wbern_stepB p hp7
  rw [← wbern_stepC p hp7]
  have hpF : IsCoprime ((p : ℤ) ^ 4) ((p - 1).factorial : ℤ) := by
    have : IsCoprime ((p ^ 4 : ℕ) : ℤ) ((p - 1).factorial : ℕ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left 4
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by rw [hp.dvd_factorial]; omega))
    exact_mod_cast this
  have hp22 : IsCoprime ((p : ℤ) ^ 2) 2 := by
    have : IsCoprime ((p ^ 2 : ℕ) : ℤ) ((2 : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact_mod_cast this
  have hp23 : IsCoprime ((p : ℤ) ^ 2) ((p - 3 : ℕ) : ℤ) := by
    have : IsCoprime ((p ^ 2 : ℕ) : ℤ) ((p - 3 : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left 2
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    exact_mod_cast this
  set E := ∑ t ∈ (univ : Finset (Fin (p - 1))).powersetCard (p - 3),
    ∏ i ∈ t, (((i : ℕ) : ℤ) + 1) with hE
  set F : ℤ := ((p - 1).factorial : ℤ) with hF
  set Cb : ℤ := (((2 * p - 1).choose (p - 1) : ℕ) : ℤ) with hCb
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := by positivity
  calc (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4] ↔ (p : ℤ) ^ 4 ∣ Cb - 1 := by
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
        push_cast
        rfl
    _ ↔ (p : ℤ) ^ 4 ∣ F * (Cb - 1) :=
        ⟨fun h => h.mul_left _, fun h => hpF.dvd_of_dvd_mul_left h⟩
    _ ↔ (p : ℤ) ^ 4 ∣ 2 * (p : ℤ) ^ 2 * E :=
        ⟨fun h => by simpa using dvd_sub h hA, fun h => by simpa using dvd_add hA h⟩
    _ ↔ (p : ℤ) ^ 2 ∣ 2 * E := by
        rw [show (p : ℤ) ^ 4 = (p : ℤ) ^ 2 * (p : ℤ) ^ 2 by ring,
          show 2 * (p : ℤ) ^ 2 * E = (p : ℤ) ^ 2 * (2 * E) by ring]
        exact mul_dvd_mul_iff_left hp2
    _ ↔ (p : ℤ) ^ 2 ∣ E := ⟨fun h => hp22.dvd_of_dvd_mul_left h, fun h => h.mul_left _⟩
    _ ↔ (p : ℤ) ^ 2 ∣ ((p - 3 : ℕ) : ℤ) * E :=
        ⟨fun h => h.mul_left _, fun h => hp23.dvd_of_dvd_mul_left h⟩
    _ ↔ (p : ℤ) ^ 2 ∣ ∑ k ∈ range p, (k : ℤ) ^ (p - 3) :=
        ⟨fun h => by simpa using dvd_sub hB h, fun h => by simpa using dvd_sub hB h⟩

theorem wolstenholme_bernoulli (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑p ∣ (bernoulli' (p - 3)).num := by
  unfold IsWolstenholmePrime
  constructor
  · rintro ⟨h7, hp, h⟩
    exact ⟨h7, hp, (wbern_main p hp h7).mp h⟩
  · rintro ⟨h7, hp, h⟩
    exact ⟨h7, hp, (wbern_main p hp h7).mpr h⟩

end OpenProofs.WolstenholmePrime
