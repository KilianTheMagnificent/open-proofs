import FormalConjectures.OEIS.«87719»
import OpenProofs.Results.OEIS.P87719_a_exists

/-!
# `OeisA87719.a_formula`

Upstream: `OeisA87719.a_formula` (category textbook), `FormalConjectures/OEIS/87719.lean` line 84.

Statement form: upstream `a n` is `Nat.find (OeisA87719.a_exists n)`, and the upstream proof of
`a_exists` is a placeholder, so any theorem whose type mentions `a` reaches it in the axiom walk.
The theorem below states `Nat.find (OpenProofs.OeisA87719.a_exists n) = …` instead, with the
checked existence proof from `P87719_a_exists`. By proof irrelevance this type is definitionally
the upstream type; the checker verifies that (`statement_match`, kernel-defeq).

Proof idea: put `M = 3 ^ n + 3 * 2 ^ n + 6`. For `k ≤ M`, `k > minFac k ^ n` holds exactly when
`k` is even and `k > 2 ^ n`, or `k ≡ 3 (mod 6)` and `k > 3 ^ n`: a number with smallest prime
factor `p ≥ 5` that exceeds `p ^ n` is composite, so it is at least `p ^ 2 ≥ 25` and above `5 ^ n`,
which is impossible below `M` (`n = 1`: `M = 15`; `n = 2`: only `26, 27` lie in `(25, 27]`;
`n ≥ 3`: `M ≤ 5 ^ n`). Hence, for `m ≤ M`, the exceeding count is
`(m / 2 - 2 ^ (n - 1)) + ((m + 3) / 6 - (3 ^ n + 3) / 6)` (induction on `m`), and the two counts
sum to `m`. Arithmetic with `3 ^ n ≡ 3 (mod 6)` and `2 ^ n ≤ 3 ^ n` shows that the exceeding count
is more than half of `m` at `m = M` and at most half for every `m < M`.
-/

open Nat
open OeisA87719

namespace OpenProofs.OeisA87719

theorem a87719_formula_le_five_pow (n : ℕ) (hn : 3 ≤ n) : 3 ^ n + 3 * 2 ^ n + 6 ≤ 5 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ, pow_succ]
    omega

theorem a87719_exceed_iff (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 3 ^ n + 3 * 2 ^ n + 6) :
    k.minFac ^ n < k ↔ (k % 2 = 0 ∧ 2 ^ n < k) ∨ (k % 6 = 3 ∧ 3 ^ n < k) := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · simp
    · simp
  rcases Nat.even_or_odd k with he | ho
  · have h2 : k.minFac = 2 := (Nat.minFac_eq_two_iff k).2 (even_iff_two_dvd.1 he)
    have hk0 : k % 2 = 0 := Nat.even_iff.1 he
    rw [h2]
    constructor
    · intro h; exact Or.inl ⟨hk0, h⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · omega
  have hk1 : k % 2 = 1 := Nat.odd_iff.1 ho
  have hne2 : k.minFac ≠ 2 := by
    intro h
    have := (Nat.minFac_eq_two_iff k).1 h
    omega
  have hprime : k.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : k.minFac ∣ k := Nat.minFac_dvd k
  rcases Nat.eq_zero_or_pos (k % 3) with h3 | h3
  · have hle3 : k.minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero h3)
    have hge2 := hprime.two_le
    have hp3 : k.minFac = 3 := by omega
    rw [hp3]
    constructor
    · intro h; exact Or.inr ⟨by omega, h⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · omega
      · exact h
  · have hne3 : k.minFac ≠ 3 := by
      intro h
      rw [h] at hdvd
      omega
    have hne4 : k.minFac ≠ 4 := by
      intro h
      rw [h] at hdvd
      have : 2 ∣ k := dvd_trans ⟨2, rfl⟩ hdvd
      omega
    have hge2 := hprime.two_le
    have hp5 : 5 ≤ k.minFac := by omega
    have hrhs : ¬ ((k % 2 = 0 ∧ 2 ^ n < k) ∨ (k % 6 = 3 ∧ 3 ^ n < k)) := by omega
    simp only [hrhs, iff_false, not_lt]
    by_contra hlt
    rw [not_le] at hlt
    have hnp : ¬ k.Prime := by
      intro hkp
      rw [hkp.minFac_eq] at hlt
      have := Nat.le_self_pow (by omega : n ≠ 0) k
      omega
    have hsq : k.minFac ^ 2 ≤ k := Nat.minFac_sq_le_self (by omega) hnp
    have h25 : 5 ^ 2 ≤ k.minFac ^ 2 := Nat.pow_le_pow_left hp5 2
    have h5n : 5 ^ n ≤ k.minFac ^ n := Nat.pow_le_pow_left hp5 n
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3n
    · norm_num at hk h25
      omega
    · norm_num at hk h25 h5n
      omega
    · have := a87719_formula_le_five_pow n h3n
      omega

theorem a87719_count_formula (n m : ℕ) (hn : 1 ≤ n) (hm : m ≤ 3 ^ n + 3 * 2 ^ n + 6) :
    countExceeding n m = (m / 2 - 2 ^ (n - 1)) + ((m + 3) / 6 - (3 ^ n + 3) / 6) := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  induction m with
  | zero =>
    simp [countExceeding]
  | succ m ih =>
    rw [a87719_countExceeding_succ, ih (by omega)]
    have hiff := a87719_exceed_iff n (m + 1) hn hm
    split_ifs with h
    · rw [hiff] at h
      omega
    · rw [hiff] at h
      omega

theorem a87719_find_eq (n : ℕ) (hn : 1 ≤ n)
    (h : ∃ m, countExceeding n m > countNotExceeding n m) :
    Nat.find h = 3 ^ n + 3 * 2 ^ n + 6 := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h23 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h36 : 3 ^ n % 6 = 3 := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have : 3 ^ j % 2 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [pow_succ]
    omega
  rw [Nat.find_eq_iff]
  constructor
  · have hc := a87719_count_formula n (3 ^ n + 3 * 2 ^ n + 6) hn le_rfl
    have hs := a87719_count_sum n (3 ^ n + 3 * 2 ^ n + 6)
    omega
  · intro m hm
    have hc := a87719_count_formula n m hn hm.le
    have hs := a87719_count_sum n m
    omega

/-- Upstream `a n` with the checked existence proof in place of the placeholder one (the two are
definitionally equal by proof irrelevance). -/
theorem a_formula {n : ℕ} (hn : n ≥ 1) :
    Nat.find (OpenProofs.OeisA87719.a_exists n) = 3 ^ n + 3 * 2 ^ n + 6 :=
  a87719_find_eq n hn _

end OpenProofs.OeisA87719
