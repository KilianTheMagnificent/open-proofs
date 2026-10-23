import FormalConjectures.Wikipedia.CongruentNumber

/-!
# 1 is not a congruent number

Upstream: `CongruentNumber.not_congruentNumber_1` (formal-conjectures, Wikipedia/CongruentNumber).
This is Fermat's right triangle theorem. Suppose `a ^ 2 + b ^ 2 = c ^ 2` and `a * b / 2 = 1` over
`ℚ`. Then `(a ^ 2 - b ^ 2) ^ 2 = c ^ 4 - 16`, and `a ^ 2 ≠ b ^ 2` because `2` is not a rational
square. Multiplying by a common denominator `L` of `a, b, c` gives integers with
`C ^ 4 - (2 * L) ^ 4 = (A ^ 2 - B ^ 2) ^ 2`, a solution of `x ^ 4 - y ^ 4 = z ^ 2` with `y, z ≠ 0`.
That equation has no such solution, by Fermat's descent on `|x|`: a minimal solution has `x, y`
coprime, so `(y ^ 2, z, x ^ 2)` is a primitive Pythagorean triple. If `y` is odd, the
classification `y ^ 2 = m ^ 2 - n ^ 2`, `x ^ 2 = m ^ 2 + n ^ 2` gives the smaller solution
`m ^ 4 - n ^ 4 = (x * y) ^ 2`. If `y` is even, `y ^ 2 = 2 * m * n` and `x ^ 2 = m ^ 2 + n ^ 2`;
classifying `(n, m, x)` (with `n` odd, say) as `n = p ^ 2 - q ^ 2`, `m = 2 * p * q`, pairwise
coprimality of `p, q, n` forces `p = ±P ^ 2`, `q = ±Q ^ 2`, `n = ±v ^ 2`, so
`P ^ 4 - Q ^ 4 = ±v ^ 2` is a smaller solution (up to swapping `P` and `Q`).
-/

open CongruentNumber

namespace OpenProofs.CongruentNumber

/-- Descent step for `y` even: from a primitive triple `m ^ 2 + n ^ 2 = x ^ 2` with
`y ^ 2 = 2 * m * n` and `n` odd we get a smaller solution of `P ^ 4 - Q ^ 4 = v ^ 2`. -/
theorem quartic_diff_descent_even_aux {m n x y : ℤ} (hx : x ^ 2 = m ^ 2 + n ^ 2)
    (hy : y ^ 2 = 2 * m * n) (hmn : Int.gcd m n = 1) (hn : n % 2 = 1) (hy0 : y ≠ 0) :
    ∃ P Q v : ℤ, Q ≠ 0 ∧ v ≠ 0 ∧ P ^ 4 - Q ^ 4 = v ^ 2 ∧ P.natAbs < x.natAbs := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hy0
    have : y ^ 2 = 0 := by rw [hy]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : 0 < n ^ 2 := by positivity
    nlinarith [sq_nonneg m]
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have ht : PythagoreanTriple n m |x| := by
    delta PythagoreanTriple
    rw [abs_mul_abs_self x]
    linear_combination (-1 : ℤ) * hx
  obtain ⟨p, q, hp1, hp2, hp3, hp4, -, -⟩ :=
    ht.coprime_classification' (by rw [Int.gcd_comm]; exact hmn) hn hxpos
  have h2y : (2 : ℤ) ∣ y := by
    apply Int.prime_two.dvd_of_dvd_pow (n := 2)
    exact ⟨2 * p * q * n, by rw [hy, hp2]; ring⟩
  obtain ⟨w, rfl⟩ := h2y
  have hw : p * q * n = w ^ 2 := by
    have h4 : (4 : ℤ) * (p * q * n) = 4 * w ^ 2 := by
      linear_combination (-1 : ℤ) * hy - 2 * n * hp2
    exact mul_left_cancel₀ (by norm_num) h4
  have hpq : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hp4
  have hpn : IsCoprime p n := by
    have := (hpq.pow_right (n := 2)).neg_right.add_mul_left_right p
    rwa [show -q ^ 2 + p * p = n by rw [hp1]; ring] at this
  have hqn : IsCoprime q n := by
    have := (hpq.symm.pow_right (n := 2)).add_mul_left_right (-q)
    rwa [show p ^ 2 + q * -q = n by rw [hp1]; ring] at this
  obtain ⟨P, hP⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (hpq.mul_right hpn)) (by rw [← hw]; ring)
  obtain ⟨Q, hQ⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (hpq.symm.mul_right hqn)) (by rw [← hw]; ring)
  obtain ⟨v, hv⟩ := Int.sq_of_gcd_eq_one
    (Int.isCoprime_iff_gcd_eq_one.mp (hpn.symm.mul_right hqn.symm)) (by rw [← hw]; ring)
  have hp0 : p ≠ 0 := by rintro rfl; apply hm0; rw [hp2]; ring
  have hq0 : q ≠ 0 := by rintro rfl; apply hm0; rw [hp2]; ring
  have hP0 : P ≠ 0 := by rintro rfl; apply hp0; rcases hP with h | h <;> rw [h] <;> ring
  have hQ0 : Q ≠ 0 := by rintro rfl; apply hq0; rcases hQ with h | h <;> rw [h] <;> ring
  have hv0 : v ≠ 0 := by rintro rfl; apply hn0; rcases hv with h | h <;> rw [h] <;> ring
  have hP4 : p ^ 2 = P ^ 4 := by rcases hP with h | h <;> rw [h] <;> ring
  have hQ4 : q ^ 2 = Q ^ 4 := by rcases hQ with h | h <;> rw [h] <;> ring
  have hxx : |x| ≤ x ^ 2 := by
    have := Int.le_self_sq |x|
    rwa [sq_abs] at this
  have hPP : P ^ 2 ≤ P ^ 4 := by
    have := Int.le_self_sq (P ^ 2)
    linarith [show (P ^ 2) ^ 2 = P ^ 4 by ring]
  have hQQ : Q ^ 2 ≤ Q ^ 4 := by
    have := Int.le_self_sq (Q ^ 2)
    linarith [show (Q ^ 2) ^ 2 = Q ^ 4 by ring]
  have hP4pos : 0 < P ^ 4 := by positivity
  have hQ4pos : 0 < Q ^ 4 := by positivity
  rcases hv with hv | hv
  · refine ⟨P, Q, v, hQ0, hv0, ?_, ?_⟩
    · rw [← hP4, ← hQ4, ← hv, hp1]
    · rw [Int.natAbs_lt_iff_sq_lt]
      linarith
  · refine ⟨Q, P, v, hP0, hv0, ?_, ?_⟩
    · linear_combination hQ4.symm - hP4.symm - hv + hp1
    · rw [Int.natAbs_lt_iff_sq_lt]
      linarith

/-- Fermat: `x ^ 4 - y ^ 4 = z ^ 2` has no solution in integers with `y ≠ 0` and `z ≠ 0`
(infinite descent on `|x|`). -/
theorem quartic_diff_ne_sq_aux (k : ℕ) :
    ∀ x y z : ℤ, x.natAbs = k → y ≠ 0 → z ≠ 0 → x ^ 4 - y ^ 4 = z ^ 2 → False := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x y z hk hy hz h
  subst hk
  have hx : x ≠ 0 := by
    rintro rfl
    have h1 : 0 < y ^ 4 := by positivity
    have h2 : 0 < z ^ 2 := by positivity
    linarith
  -- a solution with smallest `|x|` has `x` and `y` coprime
  have hcop : IsCoprime x y := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    by_contra hxy
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hxy
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hpz : (p : ℤ) ^ 2 ∣ z := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h]
      exact Dvd.intro (x1 ^ 4 - y1 ^ 4) (by ring)
    obtain ⟨z1, rfl⟩ := hpz
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hx1 : x1 ≠ 0 := right_ne_zero_of_mul hx
    refine ih x1.natAbs ?_ x1 y1 z1 rfl (right_ne_zero_of_mul hy) (right_ne_zero_of_mul hz) ?_
    · rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact lt_mul_left (Int.natAbs_pos.mpr hx1) hp.one_lt
    · apply mul_left_cancel₀ (pow_ne_zero 4 hp0)
      linear_combination h
  have hyz : IsCoprime (y ^ 2) z := by
    have h1 : IsCoprime (y ^ 4) (x ^ 4) := hcop.symm.pow
    have h2 : IsCoprime (y ^ 4) (z ^ 2) := by
      have := h1.add_mul_left_right (-1)
      rwa [show x ^ 4 + y ^ 4 * -1 = z ^ 2 by linear_combination h] at this
    have h3 : IsCoprime y z := (IsCoprime.pow_iff (by norm_num) (by norm_num)).mp h2
    exact h3.pow_left
  have hgcd : Int.gcd (y ^ 2) z = 1 := Int.isCoprime_iff_gcd_eq_one.mp hyz
  have hx2 : 0 < x ^ 2 := by positivity
  rcases Int.emod_two_eq_zero_or_one y with hye | hyo
  · -- `y` even, so `z` odd
    have hzo : z % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one z with hze | hzo
      · exfalso
        have h2 : IsUnit (2 : ℤ) := hyz.isUnit_of_dvd'
          (Dvd.dvd.pow (Int.dvd_of_emod_eq_zero hye) two_ne_zero) (Int.dvd_of_emod_eq_zero hze)
        rcases Int.isUnit_iff.mp h2 with h2 | h2 <;> norm_num at h2
      · exact hzo
    have ht : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
      delta PythagoreanTriple
      linear_combination (-1 : ℤ) * h
    obtain ⟨m, n, hm1, hm2, hm3, hm4, hm5, -⟩ :=
      ht.coprime_classification' (by rw [Int.gcd_comm]; exact hgcd) hzo hx2
    rcases hm5 with ⟨-, hno⟩ | ⟨hmo, -⟩
    · obtain ⟨P, Q, v, hQ, hv, hPQ, hlt⟩ :=
        quartic_diff_descent_even_aux hm3 hm2 hm4 hno hy
      exact ih _ hlt P Q v rfl hQ hv hPQ
    · obtain ⟨P, Q, v, hQ, hv, hPQ, hlt⟩ :=
        quartic_diff_descent_even_aux (m := n) (n := m) (x := x) (y := y) (by linear_combination hm3)
          (by linear_combination hm2) (by rw [Int.gcd_comm]; exact hm4) hmo hy
      exact ih _ hlt P Q v rfl hQ hv hPQ
  · -- `y` odd
    have hy2 : y ^ 2 % 2 = 1 := by
      rw [sq, Int.mul_emod, hyo]
      decide
    have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
      delta PythagoreanTriple
      linear_combination (-1 : ℤ) * h
    obtain ⟨m, n, hm1, hm2, hm3, -, -, -⟩ := ht.coprime_classification' hgcd hy2 hx2
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hz
      rw [hm2]; ring
    have hn2 : 0 < n ^ 2 := by positivity
    refine ih m.natAbs ?_ m n (x * y) rfl hn0 (mul_ne_zero hx hy) ?_
    · rw [Int.natAbs_lt_iff_sq_lt]
      linarith
    · linear_combination (-x ^ 2) * hm1 - (m ^ 2 - n ^ 2) * hm3

/-- `x ^ 4 - y ^ 4 = z ^ 2` has no integer solution with `y ≠ 0` and `z ≠ 0`. -/
theorem fourth_pow_sub_fourth_pow_ne_sq {x y z : ℤ} (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 :=
  fun h => quartic_diff_ne_sq_aux _ x y z rfl hy hz h

/-- Clearing denominators in a rational right triangle `(a, b, c)` of area `1` gives integers
with `C ^ 4 - (2 * L) ^ 4 = (A ^ 2 - B ^ 2) ^ 2`. -/
theorem exists_int_quartic_of_rat_triangle {a b c : ℚ} (h1 : a ^ 2 + b ^ 2 = c ^ 2)
    (hab : a * b = 2) (hsq : a ^ 2 - b ^ 2 ≠ 0) :
    ∃ A B C L : ℤ, L ≠ 0 ∧ A ^ 2 - B ^ 2 ≠ 0 ∧ C ^ 4 - (2 * L) ^ 4 = (A ^ 2 - B ^ 2) ^ 2 := by
  obtain ⟨L, hL0, hLq⟩ : ∃ L : ℤ, L ≠ 0 ∧ (L : ℚ) = a.den * b.den * c.den :=
    ⟨a.den * b.den * c.den, by positivity, by push_cast; rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℤ, (A : ℚ) = a * L :=
    ⟨a.num * (b.den * c.den), by push_cast; rw [hLq, ← Rat.mul_den_eq_num a]; ring⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, (B : ℚ) = b * L :=
    ⟨b.num * (a.den * c.den), by push_cast; rw [hLq, ← Rat.mul_den_eq_num b]; ring⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, (C : ℚ) = c * L :=
    ⟨c.num * (a.den * b.den), by push_cast; rw [hLq, ← Rat.mul_den_eq_num c]; ring⟩
  have hABC : A ^ 2 + B ^ 2 = C ^ 2 := by
    have : ((A : ℚ)) ^ 2 + (B : ℚ) ^ 2 = (C : ℚ) ^ 2 := by
      rw [hA, hB, hC]
      linear_combination (L : ℚ) ^ 2 * h1
    exact_mod_cast this
  have hAB : A * B = 2 * L ^ 2 := by
    have : (A : ℚ) * (B : ℚ) = 2 * (L : ℚ) ^ 2 := by
      rw [hA, hB]
      linear_combination (L : ℚ) ^ 2 * hab
    exact_mod_cast this
  refine ⟨A, B, C, L, hL0, ?_, ?_⟩
  · intro h0
    apply hsq
    have h0' : (A : ℚ) ^ 2 - (B : ℚ) ^ 2 = 0 := by exact_mod_cast h0
    rw [hA, hB] at h0'
    have h3 : (a ^ 2 - b ^ 2) * (L : ℚ) ^ 2 = 0 := by linear_combination h0'
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h4) (by exact_mod_cast hL0)
  · linear_combination (-(A ^ 2 + B ^ 2 + C ^ 2)) * hABC + 4 * (A * B + 2 * L ^ 2) * hAB

/-- Fermat's right triangle theorem for area `1`: no rational right triangle has area `1`. -/
theorem not_congruentNumber_1 : ¬ congruentNumber 1 := by
  rintro ⟨a, b, c, h1, h2⟩
  have hab : a * b = 2 := by
    push_cast at h2
    linear_combination -2 * h2
  have hsq : a ^ 2 - b ^ 2 ≠ 0 := by
    intro h0
    have h3 : (a - b) * (a + b) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp h3 with h3 | h3
    · have h2sq : IsSquare ((2 : ℕ) : ℚ) := ⟨a, by push_cast; linear_combination -hab - a * h3⟩
      exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp h2sq)
    · have h4 : a ^ 2 = -2 := by linear_combination a * h3 - hab
      nlinarith [sq_nonneg a]
  obtain ⟨A, B, C, L, hL, hz, h⟩ := exists_int_quartic_of_rat_triangle h1 hab hsq
  exact fourth_pow_sub_fourth_pow_ne_sq (mul_ne_zero two_ne_zero hL) hz h

end OpenProofs.CongruentNumber
