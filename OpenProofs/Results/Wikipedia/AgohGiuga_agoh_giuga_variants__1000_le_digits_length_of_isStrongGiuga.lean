import FormalConjectures.Wikipedia.AgohGiuga

/-!
# `AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga`

Upstream: `AgohGiuga.agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga` (category research solved), `FormalConjectures/Wikipedia/AgohGiuga.lean` line 232.
Proof idea: for a strong Giuga number `n` and a prime `p ∣ n`, reducing the sum mod `p` gives
`1 + (n/p) * (if p - 1 ∣ n - 1 then -1 else 0) ≡ 0`, so `p - 1 ∣ n - 1` and `n/p ≡ 1 (mod p)`.
Hence `n` is squarefree, no two prime factors satisfy `p ∣ q - 1`, and `n ∣ ∑ n/p - 1`, i.e.
`∑_{p ∣ n} 1/p > 1`. A branch and bound over the 303 primes `≤ 2000` (checked by the kernel, with
weights `⌈10^6/p⌉`) shows that any such set of primes `≤ 2000` has `∑ 1/p ≤ 0.845`. So the primes
`> 2000` contribute more than `0.155`, which needs at least `311` of them, and
`n ≥ 2001^311 > 10^999`.
-/

open scoped Nat
open AgohGiuga

namespace OpenProofs.AgohGiuga

/-- Weight `⌈10^6 / p⌉`, an upper bound for `10^6 / p`. -/
def giugaWt (p : ℕ) : ℕ := (1000000 + p - 1) / p

lemma giugaWt_spec {p : ℕ} (hp : 0 < p) : 1000000 ≤ p * giugaWt p := by
  unfold giugaWt
  have h1 := Nat.div_add_mod (1000000 + p - 1) p
  have h2 := Nat.mod_lt (1000000 + p - 1) hp
  omega

/-- Total weight of a list. -/
def giugaSumW (l : List ℕ) : ℕ := (l.map giugaWt).sum

/-- Branch and bound: `true` means every sub-selection `U` of `rem` with no `c ∣ r - 1` inside
has `cur + giugaSumW U ≤ T`. -/
noncomputable def giugaBB (T : ℕ) (f : ℕ) : List ℕ → ℕ → Bool :=
  Nat.rec (fun _ _ => false)
    (fun _ ih rem cur => List.casesOn (motive := fun _ => Bool) rem (decide (cur ≤ T))
      (fun q rest => decide (cur + giugaSumW (q :: rest) ≤ T) ||
        (ih (rest.filter (fun r => (r - 1) % q != 0)) (cur + giugaWt q) && ih rest cur))) f

theorem giugaBB_sound (T : ℕ) : ∀ (f : ℕ) (rem : List ℕ) (cur : ℕ), giugaBB T f rem cur = true →
    ∀ U : List ℕ, U.Sublist rem → (∀ c ∈ U, ∀ r ∈ U, ¬ c ∣ r - 1) →
      cur + giugaSumW U ≤ T := by
  intro f
  induction f with
  | zero =>
    intro rem cur h
    change false = true at h
    exact absurd h (by decide)
  | succ f ih =>
    intro rem cur h U hU hind
    cases rem with
    | nil =>
      change decide (cur ≤ T) = true at h
      rw [decide_eq_true_eq] at h
      rw [List.sublist_nil.mp hU]
      simpa [giugaSumW] using h
    | cons q rest =>
      change (decide (cur + giugaSumW (q :: rest) ≤ T) ||
        (giugaBB T f (rest.filter (fun r => (r - 1) % q != 0)) (cur + giugaWt q) &&
          giugaBB T f rest cur)) = true at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨h1, h2⟩
      · have : giugaSumW U ≤ giugaSumW (q :: rest) :=
          (hU.map giugaWt).sum_le_sum (fun _ _ => Nat.zero_le _)
        omega
      · rw [List.sublist_cons_iff] at hU
        rcases hU with hU | ⟨U', rfl, hU'⟩
        · exact ih rest cur h2 U hU hind
        · have hsub : U'.Sublist (rest.filter (fun r => (r - 1) % q != 0)) := by
            have := hU'.filter (fun r => (r - 1) % q != 0)
            rwa [List.filter_eq_self.mpr] at this
            intro r hr
            have := hind q List.mem_cons_self r (List.mem_cons_of_mem _ hr)
            simpa [Nat.dvd_iff_mod_eq_zero] using this
          have := ih _ _ h1 U' hsub
            (fun c hc r hr => hind c (List.mem_cons_of_mem _ hc) r (List.mem_cons_of_mem _ hr))
          simp only [giugaSumW, List.map_cons, List.sum_cons] at this ⊢
          omega

/-- Primes up to `2000` (checked against a sieve below). -/
def giugaPrimes : List ℕ := [
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
  1993, 1997, 1999]

/-- `p ≥ 2` has no prime factor `≤ 43` other than itself; for `p ≤ 2000` this means prime. -/
def giugaSieve (p : ℕ) : Bool :=
  decide (2 ≤ p) && [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43].all
    (fun d => d == p || p % d != 0)

theorem giugaPrimes_eq : giugaPrimes = (List.range 2001).filter giugaSieve := by
  decide +kernel

theorem giugaBB_ok : giugaBB 845000 303 giugaPrimes 0 = true := by
  decide +kernel

lemma giuga_sum_range_zmod (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : k ≠ 0) :
    ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ k = if p - 1 ∣ k then -1 else 0 := by
  have h3 : ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ k = ∑ x : ZMod p, x ^ k := by
    refine Finset.sum_bij (fun (i : ℕ) _ => ((i : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro a ha b hb hab
      simp only [Finset.mem_range] at ha hb
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro a _; rfl
  rw [h3]
  classical
  let emb : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hemb : Finset.univ.map emb = Finset.univ \ {0} := by
    ext x
    simp only [emb, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_sdiff, Finset.mem_singleton]
    exact isUnit_iff_ne_zero
  calc ∑ x : ZMod p, x ^ k = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, x ^ k := by
        rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, Finset.sum_singleton,
          zero_pow hk, add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ k) := by simp [emb, ← hemb, Finset.univ.sum_map emb]
    _ = if p - 1 ∣ k then -1 else 0 := by
        rw [FiniteField.sum_pow_units (ZMod p) k, ZMod.card]

lemma giuga_sum_zmod (n p : ℕ) [Fact p.Prime] (hpn : p ∣ n) (hn : 2 ≤ n) :
    ((∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) =
      ((n / p : ℕ) : ZMod p) * (if p - 1 ∣ n - 1 then -1 else 0) := by
  push_cast
  have hk : n - 1 ≠ 0 := by omega
  have h1 : ∑ i ∈ Finset.Ioo 0 n, ((i : ZMod p)) ^ (n - 1) =
      ∑ i ∈ Finset.range n, ((i : ZMod p)) ^ (n - 1) := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Ioo, Finset.mem_range] at hx ⊢
      omega
    · intro x hx hnx
      simp only [Finset.mem_Ioo, Finset.mem_range, not_and, not_lt] at hx hnx
      have : x = 0 := by omega
      subst this
      simp [zero_pow hk]
  rw [h1]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨m, rfl⟩ := hpn
  have h2 : ∀ (k m : ℕ), ∑ i ∈ Finset.range (p * m), ((i : ZMod p)) ^ k =
      (m : ZMod p) * ∑ i ∈ Finset.range p, ((i : ZMod p)) ^ k := by
    intro k m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      push_cast
      simp only [ZMod.natCast_self, zero_mul, zero_add]
      ring
  rw [h2, giuga_sum_range_zmod p hk, Nat.mul_div_cancel_left m hp0]

lemma giuga_prime_facts {n p : ℕ} (hG : IsStrongGiuga n) (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 ∧ ((n / p : ℕ) : ZMod p) = 1 := by
  have := Fact.mk hp
  obtain ⟨⟨hn1, _⟩, hdvd⟩ := hG
  have h0 : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hpn.trans hdvd)
  rw [Nat.cast_add, giuga_sum_zmod n p hpn (by omega), Nat.cast_one] at h0
  split_ifs at h0 with h
  · exact ⟨h, by linear_combination -h0⟩
  · simp at h0

lemma giuga_not_dvd_sub_one {n p q : ℕ} (hG : IsStrongGiuga n) (hp : p.Prime) (hq : q.Prime)
    (hpn : p ∣ n) (hqn : q ∣ n) : ¬ p ∣ q - 1 := by
  intro h
  have hn : 1 ≤ n := by have := hG.1.1; omega
  have h2 : p ∣ n - 1 := h.trans (giuga_prime_facts hG hq hqn).1
  have h3 : p ∣ n - (n - 1) := Nat.dvd_sub hpn h2
  rw [show n - (n - 1) = 1 by omega] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

lemma giuga_squarefree {n : ℕ} (hG : IsStrongGiuga n) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hp' : p.Prime := hp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have h := (giuga_prime_facts hG hp' hpn).2
  have hdiv : p ∣ n / p := by
    obtain ⟨k, hk⟩ := hpp
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp'.pos]
    exact dvd_mul_right _ _
  have := Fact.mk hp'
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdiv] at h
  exact zero_ne_one h

lemma giuga_sum_gt {n : ℕ} (hG : IsStrongGiuga n) : n + 1 ≤ ∑ p ∈ n.primeFactors, n / p := by
  have hsq := giuga_squarefree hG
  have hn1 : 1 < n := hG.1.1
  have hnp : ¬ n.Prime := hG.1.2
  have hA : 2 ≤ ∑ p ∈ n.primeFactors, n / p := by
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
    have h1 : n / p ≤ ∑ p ∈ n.primeFactors, n / p :=
      Finset.single_le_sum (f := fun p => n / p) (fun _ _ => Nat.zero_le _) hmem
    obtain ⟨k, hk⟩ := hpn
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k
        · omega
        · rw [hk, mul_one] at hnp; exact absurd hp hnp
      · exact h
    have : n / p = k := by rw [hk, Nat.mul_div_cancel_left k hp.pos]
    omega
  have key : ∀ q ∈ n.primeFactors, q ∣ (∑ p ∈ n.primeFactors, n / p) - 1 := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have := Fact.mk hqp
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), sub_eq_zero, Nat.cast_one,
      Nat.cast_sum, Finset.sum_eq_single q]
    · exact (giuga_prime_facts hG hqp (Nat.dvd_of_mem_primeFactors hq)).2
    · intro p hp hpq
      rw [ZMod.natCast_eq_zero_iff]
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hqn : q ∣ p * (n / p) := by
        rw [Nat.mul_div_cancel' hpd]; exact Nat.dvd_of_mem_primeFactors hq
      rcases (Nat.Prime.dvd_mul hqp).mp hqn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp h).symm hpq
      · exact h
    · intro h; exact absurd hq h
  have hdvd : n ∣ (∑ p ∈ n.primeFactors, n / p) - 1 := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact Finset.prod_primes_dvd _ (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime) key
  have := Nat.le_of_dvd (by omega) hdvd
  omega

lemma giuga_mem_primes {p : ℕ} (hp : p.Prime) (h : p ≤ 2000) : p ∈ giugaPrimes := by
  rw [giugaPrimes_eq, List.mem_filter, List.mem_range]
  refine ⟨by omega, ?_⟩
  simp only [giugaSieve, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  refine ⟨hp.two_le, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := by simp at hd; omega
  by_cases hdp : p % d = 0
  · left
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdp) with h1 | h1
    · omega
    · exact h1
  · right; exact hdp

lemma giuga_primes_le {p : ℕ} (h : p ∈ giugaPrimes) : p ≤ 2000 := by
  rw [giugaPrimes_eq, List.mem_filter, List.mem_range] at h
  omega

lemma giuga_big {n : ℕ} (hG : IsStrongGiuga n) : 10 ^ 999 ≤ n := by
  classical
  have hsq := giuga_squarefree hG
  have hA := giuga_sum_gt hG
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
  set S := n.primeFactors with hS
  set Ss := S.filter (· ≤ 2000) with hSs
  set Sl := S.filter (fun p => ¬ p ≤ 2000) with hSl
  have hsmall : ∑ p ∈ Ss, giugaWt p ≤ 845000 := by
    set U := giugaPrimes.filter (fun p => decide (p ∈ S)) with hU
    have hind : ∀ c ∈ U, ∀ r ∈ U, ¬ c ∣ r - 1 := by
      intro c hc r hr
      simp only [hU, List.mem_filter, decide_eq_true_eq] at hc hr
      exact giuga_not_dvd_sub_one hG (Nat.prime_of_mem_primeFactors hc.2)
        (Nat.prime_of_mem_primeFactors hr.2) (Nat.dvd_of_mem_primeFactors hc.2)
        (Nat.dvd_of_mem_primeFactors hr.2)
    have hb := giugaBB_sound 845000 303 giugaPrimes 0 giugaBB_ok U (List.filter_sublist) hind
    have hnd : U.Nodup := by
      apply List.Nodup.filter
      rw [giugaPrimes_eq]
      exact List.nodup_range.filter _
    have heq : Ss = U.toFinset := by
      ext p
      simp only [hSs, hU, Finset.mem_filter, List.mem_toFinset, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨giuga_mem_primes (Nat.prime_of_mem_primeFactors h1) h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, giuga_primes_le h1⟩
    rw [heq, List.sum_toFinset _ hnd]
    simpa [giugaSumW] using hb
  have hsplit : ∑ p ∈ S, n / p = ∑ p ∈ Ss, n / p + ∑ p ∈ Sl, n / p :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : 1000000 * ∑ p ∈ Ss, n / p ≤ n * ∑ p ∈ Ss, giugaWt p := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hpS).pos
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hpS
    have hw := giugaWt_spec hp0
    have hnk : n / p = k := by rw [hk, Nat.mul_div_cancel_left k hp0]
    rw [hnk, hk]
    calc 1000000 * k ≤ (p * giugaWt p) * k := Nat.mul_le_mul_right _ hw
      _ = p * k * giugaWt p := by ring
  have h2 : 2001 * ∑ p ∈ Sl, n / p ≤ Sl.card * n := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ Sl, 2001 * (n / p) ≤ ∑ p ∈ Sl, n := by
          apply Finset.sum_le_sum
          intro p hp
          have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
          have hpl : 2000 < p := by have := (Finset.mem_filter.mp hp).2; omega
          have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hpS).pos
          obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hpS
          have hnk : n / p = k := by rw [hk, Nat.mul_div_cancel_left k hp0]
          rw [hnk, hk]
          exact Nat.mul_le_mul_right _ (by omega)
      _ = Sl.card * n := by rw [Finset.sum_const, smul_eq_mul]
  have hn0 : 0 < n := by have := hG.1.1; omega
  have hL : 311 ≤ Sl.card := by
    have key : n * (2001 * 1000000) < n * (2001 * 845000 + 1000000 * Sl.card) := by
      calc n * (2001 * 1000000) < 2001 * 1000000 * (n + 1) := by nlinarith
        _ ≤ 2001 * 1000000 * ∑ p ∈ S, n / p := Nat.mul_le_mul_left _ hA
        _ = 2001 * (1000000 * ∑ p ∈ Ss, n / p) + 1000000 * (2001 * ∑ p ∈ Sl, n / p) := by
          rw [hsplit]; ring
        _ ≤ 2001 * (n * ∑ p ∈ Ss, giugaWt p) + 1000000 * (Sl.card * n) := by
          gcongr
        _ ≤ 2001 * (n * 845000) + 1000000 * (Sl.card * n) := by
          gcongr
        _ = n * (2001 * 845000 + 1000000 * Sl.card) := by ring
    have := Nat.lt_of_mul_lt_mul_left key
    omega
  have h3 : 2001 ^ Sl.card ≤ ∏ p ∈ Sl, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => by have := (Finset.mem_filter.mp hp).2; omega)
  have h4 : ∏ p ∈ Sl, p ≤ n := by
    conv_rhs => rw [← hprod]
    apply Nat.le_of_dvd
    · exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    · exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  have h5 : (10 : ℕ) ^ 999 ≤ 2001 ^ 311 := by decide +kernel
  calc 10 ^ 999 ≤ 2001 ^ 311 := h5
    _ ≤ 2001 ^ Sl.card := Nat.pow_le_pow_right (by omega) hL
    _ ≤ ∏ p ∈ Sl, p := h3
    _ ≤ n := h4

theorem agoh_giuga.variants._1000_le_digits_length_of_isStrongGiuga
    (a : ℕ) (ha : IsStrongGiuga a) : 1000 ≤ (Nat.digits 10 a).length := by
  have hbig := giuga_big ha
  have hlt : a < 10 ^ (Nat.digits 10 a).length := Nat.lt_base_pow_length_digits (by norm_num)
  by_contra h
  have h' : (Nat.digits 10 a).length ≤ 999 := by omega
  have : 10 ^ (Nat.digits 10 a).length ≤ 10 ^ 999 := Nat.pow_le_pow_right (by omega) h'
  exact absurd (lt_of_le_of_lt hbig (lt_of_lt_of_le hlt this)) (lt_irrefl _)

end OpenProofs.AgohGiuga
