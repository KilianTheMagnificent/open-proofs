import FormalConjectures.OEIS.«107247»

/-!
# `OeisA107247.known_prime_and_semiprimes`

Upstream: `OeisA107247.known_prime_and_semiprimes` (category textbook), `FormalConjectures/OEIS/107247.lean` line 78.
Proof idea: compute each value `a n` by kernel reduction (`decide`), then exhibit the
factorizations `6 = 2 * 3`, ..., `358201316657 = 71 * 5045088967`, prove the factors prime with
`norm_num` (`maxRecDepth` raised for the 10-digit prime, whose
`norm_num` certificate is deeply nested), and conclude with `Nat.Prime.mul_isAlmostPrime_two`.
-/

open OeisA107247

namespace OpenProofs.OeisA107247

theorem a107247_val_8 : a 8 = 2 := by decide
theorem a107247_val_9 : a 9 = 2 * 3 := by decide
theorem a107247_val_10 : a 10 = 2 * 11 := by decide
theorem a107247_val_11 : a 11 = 2 * 43 := by decide
theorem a107247_val_13 : a 13 = 2 * 683 := by decide
theorem a107247_val_14 : a 14 = 2 * 2731 := by decide
theorem a107247_val_16 : a 16 = 2 * 43691 := by decide
theorem a107247_val_17 : a 17 = 37 * 9419 := by decide
theorem a107247_val_27 : a 27 = 71 * 5045088967 := by decide
set_option maxRecDepth 200000 in
theorem a107247_prime_big : Nat.Prime 5045088967 := by norm_num

theorem known_prime_and_semiprimes :
  (a 8).Prime ∧
  (a 9).IsSemiprime ∧
  (a 10).IsSemiprime ∧
  (a 11).IsSemiprime ∧
  (a 13).IsSemiprime ∧
  (a 14).IsSemiprime ∧
  (a 16).IsSemiprime ∧
  (a 17).IsSemiprime ∧
  (a 27).IsSemiprime := by
  rw [a107247_val_8, a107247_val_9, a107247_val_10, a107247_val_11, a107247_val_13,
    a107247_val_14, a107247_val_16, a107247_val_17, a107247_val_27]
  refine ⟨Nat.prime_two, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Nat.Prime.mul_isAlmostPrime_two (by norm_num) a107247_prime_big⟩ <;>
    exact Nat.Prime.mul_isAlmostPrime_two (by norm_num) (by norm_num)

end OpenProofs.OeisA107247
