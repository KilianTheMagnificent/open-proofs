import FormalConjectures.OEIS.«358684»

/-!
# `OeisA358684.a_7`

Upstream: `OeisA358684.a_7` (category test), `FormalConjectures/OEIS/358684.lean` line 138.
Proof idea: `F₇ = 2^128 + 1 = 59649589127497217 * 5704689200685129054721` (Morrison-Brillhart).
Both factors are proved prime by Lucas/Pratt certificates (`lucas_primality` with an explicit
factorization of `p - 1`; the modular powers are evaluated by `reduce_mod_char`, small primes by
`norm_num`). For primes `p ≤ q`, `minFac (p * q) = p`, so `minFac F₇ = 59649589127497217`, whose
`log2` is `55`, giving `a 7 = 128 - 55 = 73`.
-/

open Nat
open OeisA358684

namespace OpenProofs.OeisA358684

/-- Lucas primality test with an explicit factorization `p - 1 = ∏ qᵢ ^ eᵢ`. -/
theorem prime_of_lucasCert (p : ℕ) (a : ZMod p) (l : List (ℕ × ℕ))
    (hprime : ∀ x ∈ l, x.1.Prime) (hprod : (l.map fun x => x.1 ^ x.2).prod = p - 1)
    (ha : a ^ (p - 1) = 1) (hd : ∀ x ∈ l, a ^ ((p - 1) / x.1) ≠ 1) : p.Prime := by
  refine lucas_primality p a ha fun q hq hqd => ?_
  rw [← hprod] at hqd
  obtain ⟨y, hy, hqy⟩ := (Prime.dvd_prod_iff hq.prime).1 hqd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have := (Nat.prime_dvd_prime_iff_eq hq (hprime x hx)).1 (hq.dvd_of_dvd_pow hqy)
  subst this
  exact hd x hx

theorem prime_18533742247 : Nat.Prime 18533742247 := by
  refine prime_of_lucasCert _ 6 [(2, 1), (3, 3), (181, 1), (1896229, 1)] ?_ ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    norm_num
  · norm_num
  · reduce_mod_char
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> reduce_mod_char <;> decide

theorem prime_116503103764643 : Nat.Prime 116503103764643 := by
  refine prime_of_lucasCert _ 2 [(2, 1), (7, 1), (449, 1), (18533742247, 1)] ?_ ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by norm_num, by norm_num, by norm_num, prime_18533742247⟩
  · norm_num
  · reduce_mod_char
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> reduce_mod_char <;> decide

theorem prime_55515497 : Nat.Prime 55515497 := by
  refine prime_of_lucasCert _ 3 [(2, 3), (6939437, 1)] ?_ ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by norm_num, by norm_num⟩
  · norm_num
  · reduce_mod_char
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨?_, ?_⟩ <;> reduce_mod_char <;> decide

theorem prime_733803839347 : Nat.Prime 733803839347 := by
  refine prime_of_lucasCert _ 2 [(2, 1), (3, 1), (2203, 1), (55515497, 1)] ?_ ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by norm_num, by norm_num, by norm_num, prime_55515497⟩
  · norm_num
  · reduce_mod_char
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> reduce_mod_char <;> decide

theorem prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  refine prime_of_lucasCert _ 3 [(2, 9), (116503103764643, 1)] ?_ ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by norm_num, prime_116503103764643⟩
  · norm_num
  · reduce_mod_char
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨?_, ?_⟩ <;> reduce_mod_char <;> decide

theorem prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 := by
  refine prime_of_lucasCert _ 21 [(2, 9), (3, 5), (5, 1), (12497, 1), (733803839347, 1)] ?_ ?_ ?_ ?_
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_733803839347⟩
  · norm_num
  · reduce_mod_char
  · simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> reduce_mod_char <;> decide

theorem minFac_mul_of_prime_le {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    minFac (p * q) = p := by
  apply le_antisymm (minFac_le_of_dvd hp.two_le (dvd_mul_right p q))
  have hm : (minFac (p * q)).Prime :=
    minFac_prime (by nlinarith [hp.two_le, hq.two_le])
  rcases (Nat.Prime.dvd_mul hm).1 (minFac_dvd _) with h | h
  · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hm hp).1 h).symm
  · rw [(Nat.prime_dvd_prime_iff_eq hm hq).1 h]; exact hpq

/-- Unfold `a` at a symbolic `n`: `unfold a` directly on `a 7` did not finish within 90 s
(presumably some defeq check tries to evaluate `minFac (fermatNumber 7)`). -/
theorem a_eq_of_minFac_eq {n p : ℕ} (h : minFac (fermatNumber n) = p) :
    a n = 2 ^ n - log2 p := by
  unfold a
  rw [h]

theorem minFac_fermatNumber_seven : minFac (fermatNumber 7) = 59649589127497217 := by
  have h : fermatNumber 7 = 59649589127497217 * 5704689200685129054721 := by
    norm_num [fermatNumber]
  rw [h]
  exact minFac_mul_of_prime_le prime_59649589127497217 prime_5704689200685129054721
    (by norm_num)

theorem a_7 : a 7 = 73 := by
  rw [a_eq_of_minFac_eq minFac_fermatNumber_seven, Nat.log2_eq_log_two]
  norm_num

end OpenProofs.OeisA358684
