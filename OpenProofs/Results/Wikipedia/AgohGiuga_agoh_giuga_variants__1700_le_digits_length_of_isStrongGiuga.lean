import FormalConjectures.Wikipedia.AgohGiuga

/-!
# `AgohGiuga.agoh_giuga.variants._1700_le_digits_length_of_isStrongGiuga`

Upstream: `AgohGiuga.agoh_giuga.variants._1700_le_digits_length_of_isStrongGiuga` (category research solved), `FormalConjectures/Wikipedia/AgohGiuga.lean` line 241.

Proof idea. Let `a` be strong Giuga and `p ∣ a` prime, `a = p * k`. Modulo `p` the sum
`∑_{0<i<a} i^(a-1)` is `k * ∑_{x : ZMod p} x^(a-1)`, which is `-k` if `p - 1 ∣ a - 1` and `0`
otherwise. So `p - 1 ∣ a - 1` and `p ∣ a / p - 1`. Hence `a` is squarefree, its prime factors
form a "normal" set (no prime factor `q` divides `p - 1` for another prime factor `p`), and
`∑_{p ∣ a} a / p ≡ 1 (mod a)`, which gives `∑_{p ∣ a} 1/p > 1`.
If `a < 10^1700`, at most 449 prime factors exceed 6000 (as `6001^450 ≥ 10^1700`), contributing
at most `449/6001`; a kernel-checked branch-and-bound over the primes up to 6000 (`chk`, with
the upper approximation `⌈6001·10^6/p⌉` of `6001·10^6/p`) shows that a normal set of primes
`≤ 6000` has reciprocal sum at most `5552/6001`. Together the sum is at most `1`: contradiction.
-/

open scoped Nat
open AgohGiuga

namespace OpenProofs.AgohGiuga

namespace Bedocchi1700

/- ### Arithmetic consequences of the strong Giuga congruence -/

theorem zmod_sum_pow_eq (p : ℕ) [Fact p.Prime] (e : ℕ) (he : e ≠ 0) :
    ∑ x : ZMod p, x ^ e = if p - 1 ∣ e then -1 else 0 := by
  classical
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : Finset.univ.map emb = Finset.univ \ {0} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, emb] using! isUnit_iff_ne_zero
  calc ∑ x : ZMod p, x ^ e = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ e := by
        rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
          zero_pow he, add_zero]
    _ = ∑ x : (ZMod p)ˣ, (x ^ e : ZMod p) := by simp [emb, ← hmap, Finset.univ.sum_map emb]
    _ = _ := by rw [FiniteField.sum_pow_units, ZMod.card]

theorem range_sum_eq_univ (p : ℕ) [Fact p.Prime] (f : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range p, f (i : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_nbij' (fun i : ℕ => (i : ZMod p)) (fun x : ZMod p => x.val) ?_ ?_ ?_ ?_ ?_
  · intros; simp
  · intro x _; simp [ZMod.val_lt]
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact ZMod.val_cast_of_lt hi
  · intro x _; simp
  · intros; rfl

theorem range_mul_sum (p k : ℕ) (f : ZMod p → ZMod p) :
    ∑ i ∈ Finset.range (p * k), f (i : ZMod p) = k * ∑ i ∈ Finset.range p, f (i : ZMod p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h : ∀ x : ℕ, (((p * k + x : ℕ)) : ZMod p) = (x : ZMod p) := by
      intro x; push_cast; simp
    simp only [h]
    push_cast
    ring

theorem key (a : ℕ) (ha : IsStrongGiuga a) (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) :
    p - 1 ∣ a - 1 ∧ p ∣ a / p - 1 := by
  have := Fact.mk hp
  obtain ⟨⟨ha1, -⟩, hdvd⟩ := ha
  obtain ⟨k, rfl⟩ := hpa
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at ha1
    · exact h
  rw [Nat.mul_div_cancel_left k hp.pos]
  have h0 : ((1 + ∑ i ∈ Finset.Ioo 0 (p * k), i ^ (p * k - 1) : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact (Dvd.intro k rfl).trans hdvd
  have he : p * k - 1 ≠ 0 := by omega
  have hIoo : ∑ i ∈ Finset.Ioo 0 (p * k), ((i : ZMod p)) ^ (p * k - 1)
      = ∑ i ∈ Finset.range (p * k), ((i : ZMod p)) ^ (p * k - 1) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp [zero_pow he]
    rfl
  push_cast at h0
  rw [hIoo, range_mul_sum p k (fun x => x ^ (p * k - 1)),
    range_sum_eq_univ p (fun x => x ^ (p * k - 1)), zmod_sum_pow_eq p _ he] at h0
  split_ifs at h0 with hdiv
  · refine ⟨hdiv, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hk]
    push_cast
    linear_combination -h0
  · simp at h0

theorem sqfree (a : ℕ) (ha : IsStrongGiuga a) : Squarefree a := by
  have ha1 : 1 < a := ha.1.1
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpa : p ∣ a := (Dvd.intro p rfl).trans hpp
  have h2 := (key a ha p hp hpa).2
  have h3 : p ∣ a / p := by
    obtain ⟨c, hc⟩ := hpp
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact Dvd.intro c rfl
  have hpos : 0 < a / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpa) hp.pos
  have h4 : p ∣ a / p - (a / p - 1) := Nat.dvd_sub h3 h2
  rw [Nat.sub_sub_self (by omega)] at h4
  exact hp.one_lt.ne' (Nat.dvd_one.mp h4)

theorem normal (a : ℕ) (ha : IsStrongGiuga a) :
    ∀ x ∈ a.primeFactors, ∀ y ∈ a.primeFactors, x ≠ y → ¬ y ∣ x - 1 := by
  intro x hx y hy _ hyx
  have ha1 : 1 < a := ha.1.1
  have h1 := (key a ha x (Nat.prime_of_mem_primeFactors hx) (Nat.dvd_of_mem_primeFactors hx)).1
  have hya : y ∣ a := Nat.dvd_of_mem_primeFactors hy
  have h2 : y ∣ a - (a - 1) := Nat.dvd_sub hya (hyx.trans h1)
  rw [Nat.sub_sub_self (by omega)] at h2
  exact (Nat.prime_of_mem_primeFactors hy).one_lt.ne' (Nat.dvd_one.mp h2)

theorem one_lt_sum (a : ℕ) (ha : IsStrongGiuga a) :
    1 < ∑ p ∈ a.primeFactors, (1 / p : ℚ) := by
  have hsq := sqfree a ha
  have ha1 : 1 < a := ha.1.1
  have hnp : ¬ a.Prime := ha.1.2
  have hprod : ∏ p ∈ a.primeFactors, p = a := Nat.prod_primeFactors_of_squarefree hsq
  have hterm : ∀ q ∈ a.primeFactors, 1 ≤ a / q := fun q hq =>
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq))
      (Nat.prime_of_mem_primeFactors hq).pos
  have hcard : 2 ≤ a.primeFactors.card := by
    by_contra h
    push Not at h
    interval_cases hc : a.primeFactors.card
    · rw [Finset.card_eq_zero] at hc
      rw [hc, Finset.prod_empty] at hprod
      omega
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      have hmem : p ∈ a.primeFactors := hp ▸ Finset.mem_singleton_self p
      rw [hp, Finset.prod_singleton] at hprod
      exact hnp (hprod ▸ Nat.prime_of_mem_primeFactors hmem)
  have hM2 : 2 ≤ ∑ q ∈ a.primeFactors, a / q := by
    calc 2 ≤ a.primeFactors.card := hcard
      _ = ∑ q ∈ a.primeFactors, 1 := by simp
      _ ≤ ∑ q ∈ a.primeFactors, a / q := Finset.sum_le_sum hterm
  have hdvd : ∀ p ∈ a.primeFactors, p ∣ (∑ q ∈ a.primeFactors, a / q) - 1 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpa := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk hpp
    have hk := (key a ha p hpp hpa).2
    have h1 : ((a / p : ℕ) : ZMod p) = 1 := by
      have h := (ZMod.natCast_eq_zero_iff _ _).mpr hk
      rw [Nat.cast_sub (hterm p hp), Nat.cast_one] at h
      exact sub_eq_zero.mp h
    have h0 : ∀ q ∈ a.primeFactors.erase p, ((a / q : ℕ) : ZMod p) = 0 := by
      intro q hq
      obtain ⟨hqp, hqS⟩ := Finset.mem_erase.mp hq
      have hqq := Nat.prime_of_mem_primeFactors hqS
      rw [ZMod.natCast_eq_zero_iff]
      have h : p ∣ a / q * q := by
        rw [Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hqS)]; exact hpa
      rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
      · exact h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hqq).mp h) (Ne.symm hqp)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), Nat.cast_sum,
      ← Finset.add_sum_erase _ _ hp, h1, Finset.sum_eq_zero h0]
    simp
  have hprodvd : a ∣ (∑ q ∈ a.primeFactors, a / q) - 1 := by
    have h := Finset.prod_primes_dvd (s := a.primeFactors) _
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hdvd
    rwa [hprod] at h
  have haM : a + 1 ≤ ∑ q ∈ a.primeFactors, a / q := by
    have := Nat.le_of_dvd (by omega) hprodvd
    omega
  have hsumQ : (∑ p ∈ a.primeFactors, (1 / p : ℚ)) * a
      = ((∑ q ∈ a.primeFactors, a / q : ℕ) : ℚ) := by
    rw [Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos : (0 : ℚ) < q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
    rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hq) hqpos.ne']
    field_simp
  have haQ : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have haMQ : (a : ℚ) + 1 ≤ ((∑ q ∈ a.primeFactors, a / q : ℕ) : ℚ) := by exact_mod_cast haM
  by_contra hcon
  push Not at hcon
  have : (∑ p ∈ a.primeFactors, (1 / p : ℚ)) * a ≤ 1 * a := mul_le_mul_of_nonneg_right hcon haQ.le
  linarith

/- ### Kernel-checked branch and bound over the primes up to 6000 -/

/-- Upper approximation `⌈6001·10^6 / p⌉` of `6001·10^6 / p`. -/
def uB (p : ℕ) : ℕ := (6001000000 + p - 1) / p

/-- Drop the elements `x` with `p ∣ x - 1`. -/
noncomputable def filt (p : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => bif Nat.beq ((x - 1) % p) 0 then filt p xs else x :: filt p xs

noncomputable def lsum : List ℕ → ℕ
  | [] => 0
  | x :: xs => uB x + lsum xs

/-- Branch and bound: `acc` is the weight of the primes chosen so far, the list holds the
remaining candidates compatible with them, and `t` is the total weight of that list. -/
noncomputable def chk : ℕ → List ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | _ + 1, [], acc, _ => Nat.ble acc 5552000000
  | n + 1, p :: ps, acc, t =>
    Nat.ble (acc + t) 5552000000 ||
      (chk n (filt p ps) (acc + uB p) (lsum (filt p ps)) && chk n ps acc (t - uB p))

def wheelList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

def wheelP (n : ℕ) : Bool := wheelList.all (fun q => !Nat.beq (n % q) 0 || Nat.beq q n)

def primeList : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
  179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
  283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
  547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
  661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
  811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
  947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
  1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
  1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373,
  1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
  1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657,
  1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
  1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987,
  1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
  2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287,
  2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423,
  2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617,
  2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
  2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903,
  2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079,
  3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257,
  3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
  3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571,
  3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727,
  3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907,
  3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057,
  4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231,
  4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409,
  4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583,
  4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751,
  4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937,
  4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087,
  5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279,
  5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443,
  5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639,
  5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791,
  5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939,
  5953, 5981, 5987
  ]

theorem primeList_eq : primeList = (List.range' 2 5999).filter wheelP := by decide +kernel

theorem chk_ok : chk 800 primeList 0 (lsum primeList) = true := by decide +kernel

theorem mem_primeList (p : ℕ) (hp : p.Prime) (h : p ≤ 6000) : p ∈ primeList := by
  rw [primeList_eq, List.mem_filter, List.mem_range'_1]
  refine ⟨⟨hp.two_le, by omega⟩, ?_⟩
  have hw : ∀ q ∈ wheelList, 2 ≤ q := by decide
  unfold wheelP
  rw [List.all_eq_true]
  intro q hq
  by_cases hd : p % q = 0
  · have hqp : q = p :=
      ((hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hd)).resolve_left
        (by have := hw q hq; omega))
    simp [hqp]
  · have hb : (p % q).beq 0 = false :=
      Bool.eq_false_iff.mpr (fun h' => hd (Nat.eq_of_beq_eq_true h'))
    simp [hb]

theorem mem_filt (p y : ℕ) (xs : List ℕ) : y ∈ filt p xs ↔ y ∈ xs ∧ ¬ p ∣ y - 1 := by
  induction xs with
  | nil => simp [filt]
  | cons x xs ih =>
    by_cases hd : p ∣ x - 1
    · have h : Nat.beq ((x - 1) % p) 0 = true := by
        rw [Nat.mod_eq_zero_of_dvd hd]; rfl
      simp only [filt, h, cond_true, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact absurd hd h2
        · exact ⟨h1, h2⟩
    · have h : Nat.beq ((x - 1) % p) 0 = false :=
        Bool.eq_false_iff.mpr (fun h' => hd (Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h')))
      simp only [filt, h, cond_false, List.mem_cons, ih]
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · subst h1; exact ⟨Or.inl rfl, hd⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2⟩

theorem sum_le_lsum (L : List ℕ) : ∀ T : Finset ℕ, T ⊆ L.toFinset → ∑ x ∈ T, uB x ≤ lsum L := by
  induction L with
  | nil =>
    intro T hT
    simp only [List.toFinset_nil, Finset.subset_empty] at hT
    subst hT; simp
  | cons x xs ih =>
    intro T hT
    simp only [lsum]
    by_cases hx : x ∈ T
    · rw [← Finset.add_sum_erase T _ hx]
      have hs : T.erase x ⊆ xs.toFinset := by
        intro y hy
        obtain ⟨hyx, hyT⟩ := Finset.mem_erase.mp hy
        have h := hT hyT
        simp only [List.mem_toFinset, List.mem_cons] at h ⊢
        exact h.resolve_left hyx
      have := ih _ hs
      omega
    · have hs : T ⊆ xs.toFinset := by
        intro y hy
        have h := hT hy
        simp only [List.mem_toFinset, List.mem_cons] at h ⊢
        exact h.resolve_left (fun h' => hx (h' ▸ hy))
      have := ih _ hs
      omega

theorem chk_sound (n : ℕ) : ∀ (L : List ℕ) (acc : ℕ), chk n L acc (lsum L) = true →
    ∀ T : Finset ℕ, T ⊆ L.toFinset → (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ y ∣ x - 1) →
    acc + ∑ x ∈ T, uB x ≤ 5552000000 := by
  induction n with
  | zero => intro L acc h; simp [chk] at h
  | succ n ih =>
    intro L acc h T hT hN
    cases L with
    | nil =>
      simp only [chk, Nat.ble_eq] at h
      simp only [List.toFinset_nil, Finset.subset_empty] at hT
      subst hT; simpa using h
    | cons p ps =>
      have hsub : lsum (p :: ps) - uB p = lsum ps := by simp [lsum]
      simp only [chk, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, hsub] at h
      rcases h with h | ⟨h1, h2⟩
      · have := sum_le_lsum (p :: ps) T hT
        omega
      · by_cases hp : p ∈ T
        · rw [← Finset.add_sum_erase T _ hp]
          have hs : T.erase p ⊆ (filt p ps).toFinset := by
            intro y hy
            obtain ⟨hyp, hyT⟩ := Finset.mem_erase.mp hy
            have h := hT hyT
            simp only [List.mem_toFinset, List.mem_cons] at h
            rw [List.mem_toFinset, mem_filt]
            exact ⟨h.resolve_left hyp, hN y hyT p hp hyp⟩
          have hN2 : ∀ x ∈ T.erase p, ∀ y ∈ T.erase p, x ≠ y → ¬ y ∣ x - 1 :=
            fun x hx y hy hxy =>
              hN x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
          have := ih _ _ h1 _ hs hN2
          omega
        · have hs : T ⊆ ps.toFinset := by
            intro y hy
            have h := hT hy
            simp only [List.mem_toFinset, List.mem_cons] at h ⊢
            exact h.resolve_left (fun h' => hp (h' ▸ hy))
          exact ih _ _ h2 _ hs hN

theorem uB_spec (p : ℕ) (hp : 0 < p) : 6001000000 ≤ uB p * p := by
  unfold uB
  have h1 := Nat.div_add_mod (6001000000 + p - 1) p
  have h2 := Nat.mod_lt (6001000000 + p - 1) hp
  rw [Nat.mul_comm] at h1
  generalize (6001000000 + p - 1) / p * p = m at h1 ⊢
  omega

theorem inv_le_uB (p : ℕ) (hp : 0 < p) : (1 / p : ℚ) ≤ (uB p : ℚ) / 6001000000 := by
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  rw [div_le_div_iff₀ hpQ (by norm_num)]
  have h : ((6001000000 : ℕ) : ℚ) ≤ ((uB p * p : ℕ) : ℚ) := by exact_mod_cast uB_spec p hp
  push_cast at h
  linarith

theorem sum_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hN : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ y ∣ x - 1) (hprod : ∏ p ∈ S, p < 10 ^ 1700) :
    ∑ p ∈ S, (1 / p : ℚ) ≤ 1 := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ 6000)]
  -- small primes: the branch and bound
  have hsub : S.filter (fun p => p ≤ 6000) ⊆ primeList.toFinset := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [List.mem_toFinset]
    exact mem_primeList p (hS p hp.1) hp.2
  have hsmallN : ∑ p ∈ S.filter (fun p => p ≤ 6000), uB p ≤ 5552000000 := by
    have := chk_sound 800 primeList 0 chk_ok _ hsub
      (fun x hx y hy hxy => hN x (Finset.mem_of_mem_filter x hx) y
        (Finset.mem_of_mem_filter y hy) hxy)
    omega
  have hsmall : ∑ p ∈ S.filter (fun p => p ≤ 6000), (1 / p : ℚ) ≤ 5552000000 / 6001000000 := by
    calc ∑ p ∈ S.filter (fun p => p ≤ 6000), (1 / p : ℚ)
        ≤ ∑ p ∈ S.filter (fun p => p ≤ 6000), (uB p : ℚ) / 6001000000 := by
          apply Finset.sum_le_sum
          intro p hp
          exact inv_le_uB p (hS p (Finset.mem_of_mem_filter p hp)).pos
      _ = ((∑ p ∈ S.filter (fun p => p ≤ 6000), uB p : ℕ) : ℚ) / 6001000000 := by
          rw [Nat.cast_sum, Finset.sum_div]
      _ ≤ 5552000000 / 6001000000 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact_mod_cast hsmallN
  -- large primes: few of them
  have hcard : (S.filter (fun p => ¬ p ≤ 6000)).card ≤ 449 := by
    by_contra hc
    have h1 : 6001 ^ (S.filter (fun p => ¬ p ≤ 6000)).card
        ≤ ∏ p ∈ S.filter (fun p => ¬ p ≤ 6000), p :=
      Finset.pow_card_le_prod _ _ _ (fun x hx => by
        rw [Finset.mem_filter] at hx; omega)
    have h2 : ∏ p ∈ S.filter (fun p => ¬ p ≤ 6000), p ≤ ∏ p ∈ S, p :=
      Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        (fun i hi _ => (hS i hi).one_lt.le)
    have h3 : 6001 ^ 450 ≤ 6001 ^ (S.filter (fun p => ¬ p ≤ 6000)).card :=
      Nat.pow_le_pow_right (by norm_num) (not_le.mp hc)
    have h4 : (10 : ℕ) ^ 1700 ≤ 6001 ^ 450 := by decide +kernel
    exact absurd (h4.trans (h3.trans (h1.trans h2))) (not_le.mpr hprod)
  have hbig : ∑ p ∈ S.filter (fun p => ¬ p ≤ 6000), (1 / p : ℚ) ≤ 449 * (1 / 6001) := by
    calc ∑ p ∈ S.filter (fun p => ¬ p ≤ 6000), (1 / p : ℚ)
        ≤ (S.filter (fun p => ¬ p ≤ 6000)).card • (1 / 6001 : ℚ) := by
          apply Finset.sum_le_card_nsmul
          intro p hp
          rw [Finset.mem_filter] at hp
          have : (6001 : ℚ) ≤ p := by exact_mod_cast (by omega : 6001 ≤ p)
          exact one_div_le_one_div_of_le (by norm_num) this
      _ ≤ 449 * (1 / 6001) := by
          rw [nsmul_eq_mul]
          have : ((S.filter (fun p => ¬ p ≤ 6000)).card : ℚ) ≤ 449 := by exact_mod_cast hcard
          nlinarith
  linarith

end Bedocchi1700

theorem agoh_giuga.variants._1700_le_digits_length_of_isStrongGiuga
    (a : ℕ) (ha : IsStrongGiuga a) :
    (Nat.digits 10 a).length > 1700 := by
  by_contra hlen
  push Not at hlen
  have hlt : a < 10 ^ 1700 := (Nat.digits_length_le_iff (by norm_num) a).mp hlen
  have hprod : ∏ p ∈ a.primeFactors, p = a :=
    Nat.prod_primeFactors_of_squarefree (Bedocchi1700.sqfree a ha)
  have h1 := Bedocchi1700.sum_le_one a.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (Bedocchi1700.normal a ha) (by rw [hprod]; exact hlt)
  have h2 := Bedocchi1700.one_lt_sum a ha
  linarith

end OpenProofs.AgohGiuga
