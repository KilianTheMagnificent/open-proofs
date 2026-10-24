import FormalConjectures.Wikipedia.WolstenholmePrime

/-!
# `WolstenholmePrime.wolstenholme_harmonic`

Upstream: `WolstenholmePrime.wolstenholme_harmonic` (category textbook), `FormalConjectures/Wikipedia/WolstenholmePrime.lean` line 80.
Proof idea: let `P(X) = ∏_{k=1}^{p-1} (X + k) ∈ ℤ[X]`, `L = (p-1)!`. Then
`P(p) = L * C(2p-1, p-1)`, `P(-p) = L` (`p - 1` even), and comparing the coefficients below
degree 4 gives `P(p) - P(-p) ≡ 2 c₁ p + 2 c₃ p³ (mod p⁴)`, where `c₁ = L * H_{p-1}` (induction)
and `p ∣ c₃` because `P ≡ X^(p-1) - 1` in `(ZMod p)[X]` (both monic of degree `p - 1`, vanishing
at all nonzero residues). Hence `L * (C(2p-1,p-1) - 1) ≡ 2 p c₁ (mod p⁴)`; as `L` and `2` are
prime to `p`, `C(2p-1,p-1) ≡ 1 (mod p⁴) ↔ p³ ∣ c₁ ↔ p³ ∣ num(H_{p-1})` (the denominator of
`H_{p-1}` divides `L`).
-/

open WolstenholmePrime Polynomial

namespace OpenProofs.WolstenholmePrime

/-- `∏_{i<n} (X + (i + 1))` over `ℤ`. -/
noncomputable def whPoly (n : ℕ) : ℤ[X] := ∏ i ∈ Finset.range n, (X + C ((i : ℤ) + 1))

theorem whPoly_succ (n : ℕ) : whPoly (n + 1) = whPoly n * (X + C ((n : ℤ) + 1)) := by
  rw [whPoly, Finset.prod_range_succ, ← whPoly]

theorem whPoly_coeff_zero (n : ℕ) : (whPoly n).coeff 0 = (n.factorial : ℤ) := by
  induction n with
  | zero => simp [whPoly]
  | succ n ih =>
    rw [whPoly_succ, mul_coeff_zero, ih]
    simp [Nat.factorial_succ]
    ring

theorem whPoly_coeff_one (n : ℕ) :
    ((whPoly n).coeff 1 : ℚ) = (n.factorial : ℚ) * harmonic n := by
  induction n with
  | zero => simp [whPoly, coeff_one]
  | succ n ih =>
    rw [whPoly_succ, mul_add, coeff_add, coeff_mul_C, show (1 : ℕ) = 0 + 1 from rfl,
      coeff_mul_X, whPoly_coeff_zero, harmonic_succ]
    push_cast
    rw [ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem wh_factorial_add (p : ℕ) :
    ∀ m : ℕ, (p + m).factorial = p.factorial * ∏ i ∈ Finset.range m, (p + i + 1)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, ← mul_assoc, ← wh_factorial_add p m, ← add_assoc,
      Nat.factorial_succ]
    ring

theorem whPoly_eval_pos (p : ℕ) (hp : 1 ≤ p) :
    (whPoly (p - 1)).eval (p : ℤ) =
      ((p - 1).factorial : ℤ) * ((2 * p - 1).choose (p - 1) : ℤ) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := 2 * p - 1) (k := p - 1) (by omega)
  have h2 : 2 * p - 1 - (p - 1) = p := by omega
  rw [h2, show 2 * p - 1 = p + (p - 1) by omega, wh_factorial_add] at h1
  have h3 : (2 * p - 1).choose (p - 1) * (p - 1).factorial =
      ∏ i ∈ Finset.range (p - 1), (p + i + 1) := by
    rw [show 2 * p - 1 = p + (p - 1) by omega]
    have := Nat.factorial_pos p
    nlinarith [h1]
  rw [whPoly, eval_prod]
  have h4 := congrArg (fun n : ℕ => (n : ℤ)) h3
  push_cast at h4
  simp only [eval_add, eval_X, eval_C]
  rw [mul_comm, h4]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem whPoly_eval_neg (n : ℕ) :
    (whPoly n).eval (-((n : ℤ) + 1)) = (-1) ^ n * (n.factorial : ℤ) := by
  rw [whPoly, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  rw [← Finset.prod_range_reflect]
  have : ∀ j ∈ Finset.range n,
      (-((n : ℤ) + 1) + (((n - 1 - j : ℕ) : ℤ) + 1)) = -((j : ℤ) + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Finset.prod_congr rfl this, Finset.prod_neg, Finset.card_range]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rfl

theorem wh_eval_sub (P : ℤ[X]) (x : ℤ) : ∃ r : ℤ,
    P.eval x - P.eval (-x) = 2 * P.coeff 1 * x + 2 * P.coeff 3 * x ^ 3 + x ^ 4 * r := by
  have hdvd : (X : ℤ[X]) ^ 4 ∣ P - (C (P.coeff 0) + C (P.coeff 1) * X + C (P.coeff 2) * X ^ 2 +
      C (P.coeff 3) * X ^ 3) := by
    rw [X_pow_dvd_iff]
    intro d hd
    interval_cases d <;>
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] <;> norm_num
  obtain ⟨R, hR⟩ := hdvd
  rw [sub_eq_iff_eq_add] at hR
  refine ⟨R.eval x - R.eval (-x), ?_⟩
  conv_lhs => rw [hR]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

theorem whPoly_map_zmod (p : ℕ) [Fact p.Prime] :
    (whPoly (p - 1)).map (Int.castRingHom (ZMod p)) = X ^ (p - 1) - 1 := by
  have hp := (Fact.out : p.Prime)
  have h2 := hp.two_le
  have hmap : (whPoly (p - 1)).map (Int.castRingHom (ZMod p)) =
      ∏ i ∈ Finset.range (p - 1), (X + C ((i : ZMod p) + 1)) := by
    rw [whPoly, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_add, map_X, map_C]
    simp
  rw [hmap]
  have hmon : ∀ i ∈ Finset.range (p - 1), (X + C ((i : ZMod p) + 1)).Monic :=
    fun i _ => monic_X_add_C _
  have hdeg : (∏ i ∈ Finset.range (p - 1), (X + C ((i : ZMod p) + 1))).degree =
      ((p - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_prod_of_monic _ _ hmon, Finset.sum_congr rfl (fun i _ => degree_X_add_C _),
      Finset.sum_const, Finset.card_range, nsmul_one]
  have hdeg' : ((X : (ZMod p)[X]) ^ (p - 1) - 1).degree = ((p - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_sub_eq_left_of_degree_lt] <;> simp
    omega
  refine eq_of_degree_le_of_eval_index_eq (s := Finset.range (p - 1))
    (v := fun i : ℕ => -((i : ZMod p) + 1)) ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have : (i : ZMod p) = j := by simpa using hij
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · rw [hdeg, Finset.card_range]
  · rw [hdeg, hdeg']
  · rw [(monic_prod_of_monic _ _ hmon).leadingCoeff, leadingCoeff_X_pow_sub_one]
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [eval_prod, Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by simp)]
    have hne : -((i : ZMod p) + 1) ≠ 0 := by
      rw [neg_ne_zero, ← Nat.cast_succ, Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact absurd (Nat.le_of_dvd (Nat.succ_pos _) h) (by omega)
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    rw [ZMod.pow_card_sub_one_eq_one hne, sub_self]

theorem whPoly_coeff_three_dvd (p : ℕ) (hp : p.Prime) (h7 : 7 < p) :
    (p : ℤ) ∣ (whPoly (p - 1)).coeff 3 := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have := congrArg (fun P => P.coeff 3) (whPoly_map_zmod p)
  simp only [coeff_map, eq_intCast] at this
  rw [this, coeff_sub, coeff_X_pow, coeff_one]
  simp
  omega

theorem wh_num_dvd_iff (q : ℚ) (a b m : ℤ) (hq : (a : ℚ) = b * q) (hcop : IsCoprime m b) :
    m ∣ q.num ↔ m ∣ a := by
  have h1 : q.num * b = a * q.den := by
    have : ((q.num * b : ℤ) : ℚ) = ((a * q.den : ℤ) : ℚ) := by
      push_cast
      rw [hq, ← Rat.mul_den_eq_num]
      ring
    exact_mod_cast this
  have hred : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  have hden : (q.den : ℤ) ∣ b := hred.dvd_of_dvd_mul_left ⟨a, by rw [h1, mul_comm]⟩
  have hcop' : IsCoprime m q.den := hcop.of_isCoprime_of_dvd_right hden
  constructor
  · intro h
    have : m ∣ a * q.den := h1 ▸ dvd_mul_of_dvd_left h b
    exact hcop'.dvd_of_dvd_mul_right this
  · intro h
    have : m ∣ q.num * b := h1.symm ▸ dvd_mul_of_dvd_left h _
    exact hcop.dvd_of_dvd_mul_right this

theorem wh_key (p : ℕ) (hp : p.Prime) (h7 : 7 < p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4] ↔
      ((p ^ 3 : ℕ) : ℤ) ∣ (harmonic (p - 1)).num := by
  set L : ℤ := ((p - 1).factorial : ℤ) with hLdef
  set c1 := (whPoly (p - 1)).coeff 1 with hc1
  obtain ⟨r, hr⟩ := wh_eval_sub (whPoly (p - 1)) (p : ℤ)
  have hpos := whPoly_eval_pos p (by omega)
  have hneg : (whPoly (p - 1)).eval (-(p : ℤ)) = L := by
    have := whPoly_eval_neg (p - 1)
    rw [show ((p - 1 : ℕ) : ℤ) + 1 = p by omega] at this
    rw [this, Even.neg_one_pow (hp.even_sub_one (by omega)), one_mul]
  obtain ⟨t, ht⟩ := whPoly_coeff_three_dvd p hp h7
  have hcopL : IsCoprime (p : ℤ) L := by
    rw [hLdef, Nat.isCoprime_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => by rw [hp.dvd_factorial] at h; omega)
  have hcop2 : IsCoprime (p : ℤ) 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hH : (c1 : ℚ) = (L : ℚ) * harmonic (p - 1) := by
    rw [hc1, whPoly_coeff_one, hLdef]
    push_cast
    rfl
  rw [show ((p ^ 3 : ℕ) : ℤ) = (p : ℤ) ^ 3 by push_cast; rfl,
    wh_num_dvd_iff (harmonic (p - 1)) c1 L _ hH hcopL.pow_left,
    Nat.ModEq.comm, Nat.modEq_iff_dvd]
  push_cast
  have hkey : L * (((2 * p - 1).choose (p - 1) : ℤ) - 1) =
      2 * c1 * p + (p : ℤ) ^ 4 * (2 * t + r) := by
    have : L * (((2 * p - 1).choose (p - 1) : ℤ) - 1) =
        (whPoly (p - 1)).eval (p : ℤ) - (whPoly (p - 1)).eval (-(p : ℤ)) := by
      rw [hpos, hneg]
      ring
    rw [this, hr, ht]
    ring
  constructor
  · intro h
    have h1 : (p : ℤ) ^ 4 ∣ 2 * c1 * p := by
      have : (p : ℤ) ^ 4 ∣ L * (((2 * p - 1).choose (p - 1) : ℤ) - 1) := dvd_mul_of_dvd_right h _
      rw [hkey] at this
      exact (dvd_add_left (dvd_mul_right _ _)).mp this
    rw [show (p : ℤ) ^ 4 = (p : ℤ) ^ 3 * p by ring] at h1
    have h2 := (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)).mp h1
    exact hcop2.pow_left.dvd_of_dvd_mul_left h2
  · intro h
    have h1 : (p : ℤ) ^ 4 ∣ L * (((2 * p - 1).choose (p - 1) : ℤ) - 1) := by
      rw [hkey]
      refine dvd_add ?_ (dvd_mul_right _ _)
      obtain ⟨u, hu⟩ := h
      exact ⟨2 * u, by rw [hu]; ring⟩
    exact hcopL.pow_left.dvd_of_dvd_mul_left h1

theorem wolstenholme_harmonic (p : ℕ) : IsWolstenholmePrime p ↔
    (p > 7) ∧ Nat.Prime p ∧ ↑(p ^ 3) ∣ (harmonic (p - 1)).num := by
  unfold IsWolstenholmePrime
  constructor
  · rintro ⟨h7, hp, h⟩
    exact ⟨h7, hp, (wh_key p hp h7).mp h⟩
  · rintro ⟨h7, hp, h⟩
    exact ⟨h7, hp, (wh_key p hp h7).mpr h⟩

end OpenProofs.WolstenholmePrime
