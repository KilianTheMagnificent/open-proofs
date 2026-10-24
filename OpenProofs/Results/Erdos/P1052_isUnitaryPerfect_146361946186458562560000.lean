import FormalConjectures.ErdosProblems.«1052»

/-!
# `Erdos1052.isUnitaryPerfect_146361946186458562560000`

Upstream: `Erdos1052.isUnitaryPerfect_146361946186458562560000` (category test), `FormalConjectures/ErdosProblems/1052.lean` line 78.
Proof idea: let `usig1052 n` be the sum of all unitary divisors of `n` (including `n`), so that
`usig1052 n = n + ∑ properUnitaryDivisors n` for `n > 0`. The unitary divisors of a coprime
product `m * n` are exactly the products of unitary divisors of `m` and `n`, so `usig1052` is
multiplicative, and the unitary divisors of a prime power `p ^ a` are `1` and `p ^ a`. With
`N = 2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313` this gives
`usig1052 N = ∏ (1 + p ^ a) = 2 * N`, checked by `norm_num`.
-/

open Erdos1052

namespace OpenProofs.Erdos1052

/-- Sum of the unitary divisors of `n`, including `n` itself. -/
def usig1052 (n : ℕ) : ℕ := ∑ d ∈ n.divisors with d.Coprime (n / d), d

theorem usig1052_eq_add {n : ℕ} (hn : 0 < n) :
    usig1052 n = n + ∑ i ∈ properUnitaryDivisors n, i := by
  have hset : n.divisors.filter (fun d => d.Coprime (n / d)) =
      insert n (properUnitaryDivisors n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, properUnitaryDivisors,
      Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hd, -⟩, hc⟩
      rcases eq_or_lt_of_le (Nat.le_of_dvd hn hd) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨Nat.pos_of_dvd_of_pos hd hn, h⟩, hd, hc⟩
    · rintro (rfl | ⟨-, hd, hc⟩)
      · exact ⟨⟨dvd_rfl, hn.ne'⟩, by rw [Nat.div_self hn]; exact Nat.coprime_one_right _⟩
      · exact ⟨⟨hd, hn.ne'⟩, hc⟩
  unfold usig1052
  rw [hset, Finset.sum_insert]
  simp [properUnitaryDivisors]

theorem usig1052_coprime_iff {m n a b : ℕ} (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) :
    (a * b).Coprime (m * n / (a * b)) ↔ a.Coprime (m / a) ∧ b.Coprime (n / b) := by
  rw [← Nat.div_mul_div_comm ha hb, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right,
    Nat.coprime_mul_iff_right]
  have h1 : a.Coprime (n / b) :=
    (hmn.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
  have h2 : b.Coprime (m / a) :=
    (hmn.symm.coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
  tauto

theorem usig1052_mul {m n : ℕ} (hmn : m.Coprime n) :
    usig1052 (m * n) = usig1052 m * usig1052 n := by
  unfold usig1052
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
      ↑((m.divisors.filter fun d => d.Coprime (m / d)) ×ˢ
        (n.divisors.filter fun d => d.Coprime (n / d))) := by
    refine hmn.mul_injOn_divisors.mono ?_
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1.1, hx.2.1⟩
  have hset : (m * n).divisors.filter (fun d => d.Coprime (m * n / d)) =
      ((m.divisors.filter fun d => d.Coprime (m / d)) ×ˢ
        (n.divisors.filter fun d => d.Coprime (n / d))).image (fun x : ℕ × ℕ => x.1 * x.2) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Nat.mem_divisors,
      Prod.exists]
    constructor
    · rintro ⟨⟨hd, hmn0⟩, hc⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 hd
      have hm0 : m ≠ 0 := left_ne_zero_of_mul hmn0
      have hn0 : n ≠ 0 := right_ne_zero_of_mul hmn0
      rw [usig1052_coprime_iff hmn ha hb] at hc
      exact ⟨a, b, ⟨⟨⟨ha, hm0⟩, hc.1⟩, ⟨⟨hb, hn0⟩, hc.2⟩⟩, rfl⟩
    · rintro ⟨a, b, ⟨⟨⟨ha, hm0⟩, hca⟩, ⟨⟨hb, hn0⟩, hcb⟩⟩, rfl⟩
      exact ⟨⟨mul_dvd_mul ha hb, mul_ne_zero hm0 hn0⟩,
        (usig1052_coprime_iff hmn ha hb).2 ⟨hca, hcb⟩⟩
  rw [hset, Finset.sum_image hinj, Finset.sum_mul_sum, Finset.sum_product]

theorem usig1052_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    usig1052 (p ^ a) = 1 + p ^ a := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hset : (p ^ a).divisors.filter (fun d => d.Coprime (p ^ a / d)) = {1, p ^ a} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd, -⟩, hc⟩
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
      rw [Nat.pow_div hi hp.pos] at hc
      by_contra hne
      push Not at hne
      have hi0 : i ≠ 0 := by rintro rfl; exact hne.1 (pow_zero p)
      have hia : i ≠ a := by rintro rfl; exact hne.2 rfl
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p hi0)
        (dvd_pow_self p (by omega)) hc
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, hpa.ne'⟩, Nat.coprime_one_left _⟩
      · refine ⟨⟨dvd_rfl, hpa.ne'⟩, ?_⟩
        rw [Nat.div_self hpa]
        exact Nat.coprime_one_right _
  unfold usig1052
  rw [hset, Finset.sum_pair]
  exact (Nat.one_lt_pow ha.ne' hp.one_lt).ne

theorem usig1052_prime {p : ℕ} (hp : p.Prime) : usig1052 p = 1 + p := by
  simpa using usig1052_prime_pow hp Nat.one_pos

theorem isUnitaryPerfect_146361946186458562560000 : IsUnitaryPerfect 146361946186458562560000 := by
  have hN : (146361946186458562560000 : ℕ) =
      2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313 := by norm_num
  have e0 : usig1052 (2^18) = 1 + 2^18 := usig1052_prime_pow (by norm_num) (by norm_num)
  have e1 : usig1052 (2^18 * 3) = usig1052 (2^18) * (1 + 3) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18) 3), usig1052_prime (by norm_num : Nat.Prime 3)]
  have e2 : usig1052 (2^18 * 3 * 5^4) = usig1052 (2^18 * 3) * (1 + 5^4) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3) (5^4)),
      usig1052_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 4)]
  have e3 : usig1052 (2^18 * 3 * 5^4 * 7) = usig1052 (2^18 * 3 * 5^4) * (1 + 7) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3 * 5^4) 7),
      usig1052_prime (by norm_num : Nat.Prime 7)]
  have e4 : usig1052 (2^18 * 3 * 5^4 * 7 * 11) = usig1052 (2^18 * 3 * 5^4 * 7) * (1 + 11) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7) 11),
      usig1052_prime (by norm_num : Nat.Prime 11)]
  have e5 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11) * (1 + 13) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11) 13),
      usig1052_prime (by norm_num : Nat.Prime 13)]
  have e6 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13) * (1 + 19) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11 * 13) 19),
      usig1052_prime (by norm_num : Nat.Prime 19)]
  have e7 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19) * (1 + 37) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19) 37),
      usig1052_prime (by norm_num : Nat.Prime 37)]
  have e8 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37) * (1 + 79) := by
    rw [usig1052_mul (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37) 79),
      usig1052_prime (by norm_num : Nat.Prime 79)]
  have e9 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79) * (1 + 109) := by
    rw [usig1052_mul
        (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79) 109),
      usig1052_prime (by norm_num : Nat.Prime 109)]
  have e10 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109) * (1 + 157) := by
    rw [usig1052_mul
        (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109) 157),
      usig1052_prime (by norm_num : Nat.Prime 157)]
  have e11 : usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157 * 313) =
      usig1052 (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157) * (1 + 313) := by
    rw [usig1052_mul
        (by norm_num : Nat.Coprime (2^18 * 3 * 5^4 * 7 * 11 * 13 * 19 * 37 * 79 * 109 * 157) 313),
      usig1052_prime (by norm_num : Nat.Prime 313)]
  have hu : usig1052 146361946186458562560000 = 2 * 146361946186458562560000 := by
    rw [hN, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
    norm_num
  have h := usig1052_eq_add (n := 146361946186458562560000) (by norm_num)
  exact ⟨by omega, by norm_num⟩

end OpenProofs.Erdos1052
