import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-!
# `Arxiv.«2607.05739».x_succ`

Upstream: `Arxiv.«2607.05739».x_succ` (category textbook), `FormalConjectures/Arxiv/2607.05739/TanArctanSum.lean` line 74.
Proof idea: `Z_{n+1} = Z_n (1 + (n+1)i)` gives `A_{n+1} = A_n - (n+1) B_n` and
`B_{n+1} = B_n + (n+1) A_n`. Modulo 3, `Z_n` is always one of `±1, ±(1+i)` (induction on
`n mod 3`), so `A_n ≢ 0 (mod 3)` and in particular `A_n ≠ 0` for every `n`. With `A_n ≠ 0`,
multiplying numerator and denominator of the right-hand side by `A_n` gives
`(B_n + (n+1) A_n) / (A_n - (n+1) B_n) = x_{n+1}` (also when that denominator is `0`).
-/

open Finset
open Arxiv.«2607.05739»

namespace OpenProofs.Arxiv.«2607.05739»

theorem tanArctan_gaussProd_succ (n : ℕ) :
    gaussProd (n + 1) = gaussProd n * (⟨1, ((n + 1 : ℕ) : ℤ)⟩ : GaussianInt) := by
  unfold gaussProd
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem tanArctan_A_succ (n : ℕ) : A (n + 1) = A n - (n + 1) * B n := by
  unfold A B
  rw [tanArctan_gaussProd_succ]
  simp [Zsqrtd.re_mul]
  ring

theorem tanArctan_B_succ (n : ℕ) : B (n + 1) = B n + (n + 1) * A n := by
  unfold A B
  rw [tanArctan_gaussProd_succ]
  simp [Zsqrtd.im_mul]
  ring

theorem tanArctan_mod3 (n : ℕ) :
    (A n : ZMod 3) ≠ 0 ∧ (B n : ZMod 3) = if n % 3 = 1 then (A n : ZMod 3) else 0 := by
  induction n with
  | zero => simp [A, B, gaussProd]
  | succ n ih =>
    rw [tanArctan_A_succ, tanArctan_B_succ]
    push_cast
    have hm : ((n : ℕ) : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
    rw [hm]
    generalize (A n : ZMod 3) = a at ih ⊢
    generalize (B n : ZMod 3) = b at ih ⊢
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [if_neg (by omega)] at ih
      rw [if_pos (by omega), h]
      revert a b; decide
    · rw [if_pos (by omega)] at ih
      rw [if_neg (by omega), h]
      revert a b; decide
    · rw [if_neg (by omega)] at ih
      rw [if_neg (by omega), h]
      revert a b; decide

theorem tanArctan_A_ne_zero (n : ℕ) : A n ≠ 0 := by
  intro h
  apply (tanArctan_mod3 n).1
  rw [h]
  simp

theorem x_succ (n : ℕ) (hn : 1 ≤ n) :
    x (n + 1) = (x n + (n + 1)) / (1 - (n + 1) * x n) := by
  have hA : (A n : ℚ) ≠ 0 := by exact_mod_cast tanArctan_A_ne_zero n
  unfold x
  rw [tanArctan_A_succ, tanArctan_B_succ]
  push_cast
  have e1 : (B n : ℚ) / A n + (n + 1) = (B n + (n + 1) * A n) / A n := by
    field_simp
  have e2 : 1 - (n + 1) * ((B n : ℚ) / A n) = (A n - (n + 1) * B n) / A n := by
    field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hA]

end OpenProofs.Arxiv.«2607.05739»
