import FormalConjectures.OEIS.«3162»

/-!
# `OeisA3162.a_is_integer`

Upstream: `OeisA3162.a_is_integer` (category textbook), `FormalConjectures/OEIS/3162.lean` line 84.

Proof idea. Write `c k = C(m, k)` and `V p = c p * ∑_{j < m} C(j, p) C(j, m - p)`. For
`p + 1 ≤ m`, with `q = m - p`, the summand of `V (p + 1) - V p` telescopes in `j`:
`c (p+1) C(j,p+1) C(j,q-1) - c p C(j,p) C(j,q) = (c (p+1) - c p) (W (j+1) - W j)` with
`W j = C(j,p+1) C(j,q)`, which follows from Pascal's rule and `(k+1) C(j+1,k+1) = (j+1) C(j,k)`.
Hence `V (p+1) - V p = c p c (p+1) (c (p+1) - c p)`, and by induction on `p`
(`a³ + (b - a)³ = b³ - 3ab(b - a)`) the partial sum of cubed ballot differences up to `p ≤ m`
equals `c p ^ 3 - 3 V p`. At `p = m / 2` this is `c p * (c p ^ 2 - 3 ∑ ...)`, so `a m` is an
integer.
-/

open OeisA3162 Finset

namespace OpenProofs.OeisA3162

/-- Termwise telescoping certificate. -/
theorem a3162_term (m p q j : ℕ) (hq : m - p = q + 1) :
    ((m.choose (p + 1) : ℤ) * ((j.choose (p + 1) : ℤ) * (j.choose q : ℤ)) -
        (m.choose p : ℤ) * ((j.choose p : ℤ) * (j.choose (q + 1) : ℤ))) =
      ((m.choose (p + 1) : ℤ) - (m.choose p : ℤ)) *
        (((j + 1).choose (p + 1) : ℤ) * ((j + 1).choose (q + 1) : ℤ) -
          ((j.choose (p + 1) : ℤ) * (j.choose (q + 1) : ℤ))) := by
  have h1 := Nat.add_one_mul_choose_eq j p
  have h2 := Nat.add_one_mul_choose_eq j q
  have h3 := Nat.choose_succ_right_eq m p
  rw [hq] at h3
  rw [Nat.choose_succ_succ j p] at h1 ⊢
  rw [Nat.choose_succ_succ j q] at h2 ⊢
  have h1' : ((j : ℤ) + 1) * (j.choose p : ℤ) =
      ((j.choose p : ℤ) + (j.choose (p + 1) : ℤ)) * ((p : ℤ) + 1) := by exact_mod_cast h1
  have h2' : ((j : ℤ) + 1) * (j.choose q : ℤ) =
      ((j.choose q : ℤ) + (j.choose (q + 1) : ℤ)) * ((q : ℤ) + 1) := by exact_mod_cast h2
  have h3' : (m.choose (p + 1) : ℤ) * ((p : ℤ) + 1) = (m.choose p : ℤ) * ((q : ℤ) + 1) := by
    exact_mod_cast h3
  have key : (m.choose p : ℤ) * (j.choose q : ℤ) * ((j.choose p : ℤ) + (j.choose (p + 1) : ℤ)) =
      (m.choose (p + 1) : ℤ) * (j.choose p : ℤ) * ((j.choose q : ℤ) + (j.choose (q + 1) : ℤ)) := by
    apply mul_left_cancel₀ (show ((p : ℤ) + 1) * ((q : ℤ) + 1) ≠ 0 by positivity)
    linear_combination (-((q : ℤ) + 1) * (m.choose p : ℤ) * (j.choose q : ℤ)) * h1' +
      (((p : ℤ) + 1) * (m.choose (p + 1) : ℤ) * (j.choose p : ℤ)) * h2' -
      (((j : ℤ) + 1) * (j.choose p : ℤ) * (j.choose q : ℤ)) * h3'
  push_cast
  linear_combination key

/-- One step of the induction: `V (p + 1) - V p = c p c (p+1) (c (p+1) - c p)`. -/
theorem a3162_step (m p : ℕ) (hp : p + 1 ≤ m) :
    (m.choose (p + 1) : ℤ) *
        ∑ j ∈ range m, (j.choose (p + 1) : ℤ) * (j.choose (m - (p + 1)) : ℤ) -
      (m.choose p : ℤ) * ∑ j ∈ range m, (j.choose p : ℤ) * (j.choose (m - p) : ℤ) =
      (m.choose p : ℤ) * (m.choose (p + 1) : ℤ) *
        ((m.choose (p + 1) : ℤ) - (m.choose p : ℤ)) := by
  obtain ⟨q, hq⟩ : ∃ q, m - p = q + 1 := ⟨m - p - 1, by omega⟩
  have hq' : m - (p + 1) = q := by omega
  rw [hq', hq, mul_sum, mul_sum, ← sum_sub_distrib,
    sum_congr rfl (fun j _ => a3162_term m p q j hq), ← mul_sum,
    sum_range_sub (fun j => ((j.choose (p + 1) : ℕ) : ℤ) * ((j.choose (q + 1) : ℕ) : ℤ)) m]
  have hsymm : m.choose (q + 1) = m.choose p := by
    rw [← hq]; exact Nat.choose_symm (by omega)
  simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_mul, sub_zero, hsymm]
  ring

/-- Partial sums of cubed ballot differences. -/
theorem a3162_cubes (m p : ℕ) (hp : p ≤ m) :
    ∑ k ∈ range (p + 1),
        ((m.choose k : ℤ) - if k = 0 then 0 else (m.choose (k - 1) : ℤ)) ^ 3 =
      (m.choose p : ℤ) ^ 3 -
        3 * ((m.choose p : ℤ) * ∑ j ∈ range m, (j.choose p : ℤ) * (j.choose (m - p) : ℤ)) := by
  induction p with
  | zero =>
    have h0 : ∑ j ∈ range m, (j.choose 0 : ℤ) * (j.choose (m - 0) : ℤ) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [mem_range] at hj
      rw [Nat.choose_eq_zero_of_lt (n := j) (k := m - 0) (by omega)]
      simp
    rw [h0]
    simp
  | succ p ih =>
    have step := a3162_step m p hp
    rw [sum_range_succ, ih (by omega)]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    linear_combination 3 * step

theorem a_is_integer (n : ℕ) : (a n).den = 1 := by
  have hc : (n.choose (n / 2) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.div_le_self n 2)).ne'
  have hsum := a3162_cubes n (n / 2) (Nat.div_le_self n 2)
  have ha : a n = (((n.choose (n / 2) : ℤ) ^ 2 -
      3 * ∑ j ∈ range n, (j.choose (n / 2) : ℤ) * (j.choose (n - n / 2) : ℤ) : ℤ) : ℚ) := by
    simp only [a]
    rw [div_eq_iff hc]
    have hq := congrArg (fun z : ℤ => (z : ℚ)) hsum
    push_cast at hq
    rw [hq]
    push_cast
    ring
  rw [ha]
  exact Rat.den_intCast _

end OpenProofs.OeisA3162
