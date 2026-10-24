import FormalConjectures.Mathoverflow.«339137»

/-!
# `Mathoverflow339137.mathoverflow_339137_probabilistic`

Upstream: `Mathoverflow339137.mathoverflow_339137_probabilistic` (category textbook), `FormalConjectures/Mathoverflow/339137.lean` line 70.
Proof idea: generating functions. The distribution of `indepSum X Y` at `n` is the convolution
`∑' x, X x * Y (n - x)` (`op339_indepSum_apply`); after shifting both supports to start at a lower
bound, it is the coefficient of the product of the two coefficient polynomials (`op339_conv`).
(→) Given `X`, `Y`, form `P0`, `Q0` with coefficients `X (a + i)`, `Y (b + j)` and divide by the
leading coefficients to make them monic; their product has equal nonzero coefficients (since
`X + Y` is uniform) and is monic, hence is a 0-1 polynomial; the polynomial statement makes `P`,
`Q` 0-1, so `X`, `Y` are constant on their supports, hence uniform. (←) Given monic `P`, `Q` with
nonnegative coefficients, let `X i = P.coeff i / P(1)`, `Y j = Q.coeff j / Q(1)`; then
`X + Y` has law `R.coeff n / (P(1) Q(1))`, uniform on its support because `R` is 0-1; the
probabilistic statement makes `X` uniform, so all nonzero coefficients of `P` equal its leading
coefficient `1`.
-/

open scoped Polynomial
open Mathoverflow339137

namespace OpenProofs.Mathoverflow339137

theorem op339_indepSum_apply (X Y : PMF ℤ) (n : ℤ) :
    Green28.indepSum X Y n = ∑' x, X x * Y (n - x) := by
  unfold Green28.indepSum
  show (X.bind fun x => Y.bind fun y => PMF.pure (x + y)) n = _
  rw [PMF.bind_apply]
  congr 1
  funext x
  congr 1
  rw [PMF.bind_apply, tsum_eq_single (n - x)]
  · simp [PMF.pure_apply]
  · intro y hy
    rw [PMF.pure_apply, if_neg (by omega), mul_zero]

theorem op339_conv (X Y : PMF ℤ) (a b : ℤ) (hX : ∀ x < a, X x = 0) (hY : ∀ y < b, Y y = 0)
    (m : ℕ) :
    (Green28.indepSum X Y (a + b + m)).toReal =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (X (a + p.1)).toReal * (Y (b + p.2)).toReal := by
  rw [op339_indepSum_apply, tsum_eq_sum (s := (Finset.range (m + 1)).image (fun i : ℕ => a + (i : ℤ)))]
  · rw [Finset.sum_image (by intro i _ j _ h; simpa using h),
      ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ENNReal.toReal_mul]
    have him : i ≤ m := by simp at hi; omega
    congr 3
    push_cast [him]
    ring
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hx
    by_cases h1 : x < a
    · rw [hX x h1, zero_mul]
    by_cases h2 : x > a + m
    · rw [hY _ (by omega), mul_zero]
    · exact absurd (by omega) (hx (x - a).toNat (by omega))

theorem op339_poly (f : ℕ → ℝ) (hf : (Function.support f).Finite) :
    ∃ p : ℝ[X], ∀ i, p.coeff i = f i := by
  refine ⟨∑ i ∈ hf.toFinset, Polynomial.C (f i) * Polynomial.X ^ i, fun i => ?_⟩
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (by simpa using h : f i = 0).symm

theorem op339_pmf (f : ℤ → ℝ) (s : Finset ℤ) (hf0 : ∀ k, 0 ≤ f k) (hs : ∀ k ∉ s, f k = 0)
    (hsum : ∑ k ∈ s, f k = 1) : ∃ X : PMF ℤ, ∀ k, X k = ENNReal.ofReal (f k) :=
  ⟨PMF.ofFinset (fun k => ENNReal.ofReal (f k)) s
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hf0 k), hsum, ENNReal.ofReal_one])
    (by intro k hk; simp [hs k hk]), fun k => rfl⟩

theorem op339_uniform_const (X : PMF ℤ) (h : Green28.IsUniformOnSupport X) :
    ∀ x y, X x ≠ 0 → X y ≠ 0 → X x = X y := by
  obtain ⟨s, hs, rfl⟩ := h
  intro x y hx hy
  rw [PMF.uniformOfFinset_apply] at *
  split_ifs at * <;> simp_all

theorem op339_const_uniform (X : PMF ℤ) (hf : X.support.Finite)
    (hc : ∀ x y, X x ≠ 0 → X y ≠ 0 → X x = X y) : Green28.IsUniformOnSupport X := by
  obtain ⟨x0, hx0⟩ := X.support_nonempty
  have hs : hf.toFinset.Nonempty := ⟨x0, by simpa using hx0⟩
  refine ⟨hf.toFinset, hs, ?_⟩
  have hsum : ∑ x ∈ hf.toFinset, X x = 1 := by
    rw [← X.tsum_coe, tsum_eq_sum]
    intro x hx
    simpa using hx
  have hconst : ∀ x ∈ hf.toFinset, X x = X x0 := fun x hx => hc x x0 (by simpa using hx) hx0
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  ext x
  rw [PMF.uniformOfFinset_apply]
  split_ifs with hx
  · rw [hconst x hx]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)
  · simpa using hx

theorem op339_monic_zeroOne (R : ℝ[X]) (hR : R.Monic)
    (hc : ∀ i j, R.coeff i ≠ 0 → R.coeff j ≠ 0 → R.coeff i = R.coeff j) : IsZeroOne R := by
  show R.coeffs ⊆ {1}
  intro c hc'
  rw [Polynomial.mem_coeffs_iff] at hc'
  obtain ⟨n, hn, rfl⟩ := hc'
  rw [Finset.mem_singleton]
  have h1 : R.coeff R.natDegree = 1 := hR
  rw [hc n R.natDegree (Polynomial.mem_support_iff.mp hn) (by rw [h1]; exact one_ne_zero), h1]

theorem op339_poly_of_pmf (X : PMF ℤ) (hXf : X.support.Finite) (a : ℤ)
    (hX0 : ∀ x < a, X x = 0) :
    ∃ P0 : ℝ[X], (∀ i : ℕ, P0.coeff i = (X (a + i)).toReal) ∧ 0 < P0.leadingCoeff := by
  obtain ⟨P0, hP0⟩ := op339_poly (fun i => (X (a + i)).toReal) (by
    apply (hXf.preimage (f := fun i : ℕ => a + (i : ℤ)) (by intro i _ j _ h; simpa using h)).subset
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_preimage, PMF.mem_support_iff]
    intro h
    simp [h] at hi)
  refine ⟨P0, hP0, ?_⟩
  have hne : P0 ≠ 0 := by
    obtain ⟨x0, hx0⟩ := X.support_nonempty
    rw [PMF.mem_support_iff] at hx0
    have hax : a ≤ x0 := by
      by_contra h
      exact hx0 (hX0 x0 (by omega))
    intro h
    have := hP0 (x0 - a).toNat
    rw [h, Polynomial.coeff_zero, show a + (((x0 - a).toNat : ℕ) : ℤ) = x0 by omega] at this
    exact hx0 (((ENNReal.toReal_eq_zero_iff _).mp this.symm).resolve_right (PMF.apply_ne_top _ _))
  have hnn : 0 ≤ P0.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hP0]
    exact ENNReal.toReal_nonneg
  exact lt_of_le_of_ne hnn (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hne))

theorem op339_normalize (P0 : ℝ[X]) (h : 0 < P0.leadingCoeff) :
    (Polynomial.C P0.leadingCoeff⁻¹ * P0).Monic := by
  unfold Polynomial.Monic
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ h.ne']

theorem op339_const_of_zeroOne (X : PMF ℤ) (a : ℤ) (hX0 : ∀ x < a, X x = 0) (l : ℝ) (hl : l ≠ 0)
    (P : ℝ[X]) (hPc : ∀ i : ℕ, P.coeff i = l * (X (a + i)).toReal) (hz : IsZeroOne P) :
    ∀ x y, X x ≠ 0 → X y ≠ 0 → X x = X y := by
  have key : ∀ x, X x ≠ 0 → l * (X x).toReal = 1 := by
    intro x hx
    have hax : a ≤ x := by
      by_contra h
      exact hx (hX0 x (by omega))
    have hc := hPc (x - a).toNat
    rw [show a + (((x - a).toNat : ℕ) : ℤ) = x by omega] at hc
    rw [← hc]
    apply Finset.mem_singleton.mp
    apply hz
    rw [Polynomial.mem_coeffs_iff]
    refine ⟨(x - a).toNat, Polynomial.mem_support_iff.mpr ?_, rfl⟩
    rw [hc]
    refine mul_ne_zero hl ?_
    intro h0
    exact hx (((ENNReal.toReal_eq_zero_iff _).mp h0).resolve_right (PMF.apply_ne_top _ _))
  intro x y hx hy
  have h := (key x hx).trans (key y hy).symm
  rw [mul_right_inj' hl] at h
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp h

theorem op339_fwd (hA : type_of% Mathoverflow339137.mathoverflow_339137) :
    type_of% Green28.green_28 := by
  intro X Y ⟨hXf, hYf, hU⟩
  obtain ⟨a, ha⟩ := hXf.bddBelow
  obtain ⟨b, hb⟩ := hYf.bddBelow
  have hX0 : ∀ x < a, X x = 0 := fun x hx => by
    by_contra h
    have := ha ((PMF.mem_support_iff _ _).mpr h)
    omega
  have hY0 : ∀ y < b, Y y = 0 := fun y hy => by
    by_contra h
    have := hb ((PMF.mem_support_iff _ _).mpr h)
    omega
  obtain ⟨P0, hP0, hlP⟩ := op339_poly_of_pmf X hXf a hX0
  obtain ⟨Q0, hQ0, hlQ⟩ := op339_poly_of_pmf Y hYf b hY0
  have hconv : ∀ m : ℕ, (P0 * Q0).coeff m = (Green28.indepSum X Y (a + b + m)).toReal := by
    intro m
    rw [Polynomial.coeff_mul, op339_conv X Y a b hX0 hY0 m]
    simp [hP0, hQ0]
  have hPc : ∀ i : ℕ, (Polynomial.C P0.leadingCoeff⁻¹ * P0).coeff i =
      P0.leadingCoeff⁻¹ * (X (a + i)).toReal := by
    intro i
    rw [Polynomial.coeff_C_mul, hP0]
  have hQc : ∀ i : ℕ, (Polynomial.C Q0.leadingCoeff⁻¹ * Q0).coeff i =
      Q0.leadingCoeff⁻¹ * (Y (b + i)).toReal := by
    intro i
    rw [Polynomial.coeff_C_mul, hQ0]
  have hRc : ∀ m : ℕ, (Polynomial.C P0.leadingCoeff⁻¹ * P0 *
      (Polynomial.C Q0.leadingCoeff⁻¹ * Q0)).coeff m =
      P0.leadingCoeff⁻¹ * Q0.leadingCoeff⁻¹ * (Green28.indepSum X Y (a + b + m)).toReal := by
    intro m
    rw [show Polynomial.C P0.leadingCoeff⁻¹ * P0 * (Polynomial.C Q0.leadingCoeff⁻¹ * Q0) =
      Polynomial.C (P0.leadingCoeff⁻¹ * Q0.leadingCoeff⁻¹) * (P0 * Q0) by
        rw [Polynomial.C_mul]; ring, Polynomial.coeff_C_mul, hconv]
  have hZc := op339_uniform_const _ hU
  have hR : IsZeroOne (Polynomial.C P0.leadingCoeff⁻¹ * P0 *
      (Polynomial.C Q0.leadingCoeff⁻¹ * Q0)) := by
    apply op339_monic_zeroOne _ ((op339_normalize P0 hlP).mul (op339_normalize Q0 hlQ))
    intro i j hi hj
    rw [hRc] at hi hj ⊢
    rw [hRc]
    have hi' : Green28.indepSum X Y (a + b + i) ≠ 0 := by
      intro h
      rw [h] at hi
      simp at hi
    have hj' : Green28.indepSum X Y (a + b + j) ≠ 0 := by
      intro h
      rw [h] at hj
      simp at hj
    rw [hZc _ _ hi' hj']
  obtain ⟨hPz, hQz⟩ := hA _ _ _ (op339_normalize P0 hlP) (op339_normalize Q0 hlQ)
    (by
      intro c hc
      rw [Polynomial.mem_coeffs_iff] at hc
      obtain ⟨n, -, rfl⟩ := hc
      rw [hPc]
      exact mul_nonneg (inv_nonneg.mpr hlP.le) ENNReal.toReal_nonneg)
    (by
      intro c hc
      rw [Polynomial.mem_coeffs_iff] at hc
      obtain ⟨n, -, rfl⟩ := hc
      rw [hQc]
      exact mul_nonneg (inv_nonneg.mpr hlQ.le) ENNReal.toReal_nonneg)
    rfl hR
  exact ⟨op339_const_uniform X hXf
      (op339_const_of_zeroOne X a hX0 _ (inv_ne_zero hlP.ne') _ hPc hPz),
    op339_const_uniform Y hYf
      (op339_const_of_zeroOne Y b hY0 _ (inv_ne_zero hlQ.ne') _ hQc hQz)⟩

theorem op339_pmf_of_poly (P : ℝ[X]) (hP : P.Monic) (hp' : ∀ i, 0 ≤ P.coeff i) :
    0 < P.eval 1 ∧ ∃ X : PMF ℤ, X.support.Finite ∧ (∀ x < 0, X x = 0) ∧
      ∀ i : ℕ, X i = ENNReal.ofReal (P.coeff i / P.eval 1) := by
  have hev : P.eval 1 = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i := by
    rw [Polynomial.eval_eq_sum_range]
    simp
  have hpos : 0 < P.eval 1 := by
    rw [hev]
    refine Finset.sum_pos' (fun i _ => hp' i) ⟨P.natDegree, by simp, ?_⟩
    rw [hP.coeff_natDegree]
    exact one_pos
  refine ⟨hpos, ?_⟩
  set s : Finset ℤ := (Finset.range (P.natDegree + 1)).image (fun i : ℕ => (i : ℤ)) with hs_def
  have hout : ∀ k ∉ s, (if 0 ≤ k then P.coeff k.toNat / P.eval 1 else 0) = 0 := by
    intro k hk
    split_ifs with h
    · have : P.natDegree < k.toNat := by
        by_contra hc
        apply hk
        rw [hs_def, Finset.mem_image]
        exact ⟨k.toNat, by simp; omega, by omega⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, zero_div]
    · rfl
  obtain ⟨X, hX⟩ := op339_pmf (fun k : ℤ => if 0 ≤ k then P.coeff k.toNat / P.eval 1 else 0) s
    (by
      intro k
      split_ifs
      · exact div_nonneg (hp' _) hpos.le
      · exact le_refl 0)
    hout
    (by
      rw [hs_def, Finset.sum_image (by intro i _ j _ h; simpa using h)]
      simp only [Nat.cast_nonneg, if_true, Int.toNat_natCast]
      rw [← Finset.sum_div, ← hev, div_self hpos.ne'])
  refine ⟨X, ?_, ?_, ?_⟩
  · apply s.finite_toSet.subset
    intro k hk
    rw [PMF.mem_support_iff, hX] at hk
    by_contra hc
    apply hk
    rw [hout k hc, ENNReal.ofReal_zero]
  · intro x hx
    rw [hX, if_neg (by omega), ENNReal.ofReal_zero]
  · intro i
    rw [hX, if_pos (by positivity), Int.toNat_natCast]

theorem op339_zeroOne_of_uniform (P : ℝ[X]) (hP : P.Monic) (hp' : ∀ i, 0 ≤ P.coeff i)
    (hpos : 0 < P.eval 1) (X : PMF ℤ) (hXc : ∀ i : ℕ, X i = ENNReal.ofReal (P.coeff i / P.eval 1))
    (hu : Green28.IsUniformOnSupport X) : IsZeroOne P := by
  apply op339_monic_zeroOne P hP
  intro i j hi hj
  have hne : ∀ i : ℕ, P.coeff i ≠ 0 → X i ≠ 0 := by
    intro i hi
    rw [hXc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (lt_of_le_of_ne (hp' i) (Ne.symm hi)) hpos
  have h := op339_uniform_const X hu i j (hne i hi) (hne j hj)
  rw [hXc, hXc, ENNReal.ofReal_eq_ofReal_iff (div_nonneg (hp' _) hpos.le)
    (div_nonneg (hp' _) hpos.le)] at h
  exact (div_left_inj' hpos.ne').mp h

theorem op339_bwd (hB : type_of% Green28.green_28) :
    type_of% Mathoverflow339137.mathoverflow_339137 := by
  intro P Q R hP hQ hp hq hRPQ hR
  have hp' : ∀ i, 0 ≤ P.coeff i := fun i => by
    by_cases h : P.coeff i = 0
    · rw [h]
    · exact hp _ (Polynomial.mem_coeffs_iff.mpr ⟨i, Polynomial.mem_support_iff.mpr h, rfl⟩)
  have hq' : ∀ i, 0 ≤ Q.coeff i := fun i => by
    by_cases h : Q.coeff i = 0
    · rw [h]
    · exact hq _ (Polynomial.mem_coeffs_iff.mpr ⟨i, Polynomial.mem_support_iff.mpr h, rfl⟩)
  obtain ⟨hP1, X, hXf, hX0, hXc⟩ := op339_pmf_of_poly P hP hp'
  obtain ⟨hQ1, Y, hYf, hY0, hYc⟩ := op339_pmf_of_poly Q hQ hq'
  have hconv : ∀ m : ℕ, (Green28.indepSum X Y m).toReal = R.coeff m / (P.eval 1 * Q.eval 1) := by
    intro m
    have := op339_conv X Y 0 0 hX0 hY0 m
    simp only [zero_add] at this
    rw [this, hRPQ, Polynomial.coeff_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hXc, hYc, ENNReal.toReal_ofReal (div_nonneg (hp' _) hP1.le),
      ENNReal.toReal_ofReal (div_nonneg (hq' _) hQ1.le), div_mul_div_comm]
  have hZneg : ∀ n < 0, Green28.indepSum X Y n = 0 := by
    intro n hn
    rw [op339_indepSum_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    by_cases hx : x < 0
    · rw [hX0 x hx, zero_mul]
    · rw [hY0 (n - x) (by omega), mul_zero]
  have hZ : ∀ n : ℤ, Green28.indepSum X Y n ≠ 0 → ∃ m : ℕ, n = m ∧ R.coeff m ≠ 0 := by
    intro n hn
    have hn0 : 0 ≤ n := by
      by_contra h
      exact hn (hZneg n (by omega))
    refine ⟨n.toNat, by omega, ?_⟩
    intro hc
    apply hn
    have := hconv n.toNat
    rw [hc, zero_div, show ((n.toNat : ℕ) : ℤ) = n by omega] at this
    exact ((ENNReal.toReal_eq_zero_iff _).mp this).resolve_right (PMF.apply_ne_top _ _)
  have hZf : (Green28.indepSum X Y).support.Finite := by
    apply ((Finset.range (R.natDegree + 1)).image (fun i : ℕ => (i : ℤ))).finite_toSet.subset
    intro n hn
    obtain ⟨m, rfl, hm⟩ := hZ n hn
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Nat.cast_inj,
      exists_eq_right]
    exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hm)
  have hRc : ∀ i j, R.coeff i ≠ 0 → R.coeff j ≠ 0 → R.coeff i = R.coeff j := by
    intro i j hi hj
    have h1 : ∀ i, R.coeff i ≠ 0 → R.coeff i = 1 := fun i hi =>
      Finset.mem_singleton.mp
        (hR (Polynomial.mem_coeffs_iff.mpr ⟨i, Polynomial.mem_support_iff.mpr hi, rfl⟩))
    rw [h1 i hi, h1 j hj]
  have hZc : ∀ x y, Green28.indepSum X Y x ≠ 0 → Green28.indepSum X Y y ≠ 0 →
      Green28.indepSum X Y x = Green28.indepSum X Y y := by
    intro x y hx hy
    obtain ⟨m, rfl, hm⟩ := hZ x hx
    obtain ⟨m', rfl, hm'⟩ := hZ y hy
    rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), hconv,
      hconv, hRc m m' hm hm']
  obtain ⟨hXu, hYu⟩ := hB X Y ⟨hXf, hYf, op339_const_uniform _ hZf hZc⟩
  exact ⟨op339_zeroOne_of_uniform P hP hp' hP1 X hXc hXu,
    op339_zeroOne_of_uniform Q hQ hq' hQ1 Y hYc hYu⟩

theorem mathoverflow_339137_probabilistic :
    type_of% Mathoverflow339137.mathoverflow_339137 ↔ type_of% Green28.green_28 :=
  ⟨op339_fwd, op339_bwd⟩

end OpenProofs.Mathoverflow339137
