import FormalConjectures.Wikipedia.AgohGiuga

/-!
# `AgohGiuga.agoh_giuga.variants.equivalence`

Upstream: `AgohGiuga.agoh_giuga.variants.equivalence` (category research solved), `FormalConjectures/Wikipedia/AgohGiuga.lean` line 75.
Proof idea: we prove, for every `n ≥ 2`, that Agoh's condition
`n² ∣ n·num(B'_{n-1}) + den(B'_{n-1})` is equivalent to Giuga's `n ∣ 1 + ∑_{0<i<n} i^{n-1}`.
`n = 2`: both hold. Even `n ≥ 4`: `B'_{n-1} = 0`, so Agoh's condition reads `n² ∣ 1`, false; and
reflecting `i ↦ n - i` gives `S ≡ -S (mod n)` for the odd exponent, so `n ∣ 1 + S` would force
`n ∣ 2`. Odd `n ≥ 3`: call `x` `n`-integral when `x.den` is coprime to `n`. Mathlib's
von Staudt–Clausen theorem gives that `n·B_{2m}` is `n`-integral, and `B_1 = -1/2`, `B_{odd≥3} = 0`
are `n`-integral. Faulhaber gives `S = n·B_{n-1} + n·Y` with `Y` `n`-integral, so Giuga's condition
is `n`-integrality of `1/n + B_{n-1}`. Writing `B = N/D`, that is equivalent to `n² ∣ nN + D`:
one way by Bézout (`uN + vD = 1`) and `n`-integrality of `n·B`, the other by two coprimality
cancellations (`n ∣ nN + D`, hence `n ∣ D`, hence `n² ∣ nN + D`).
-/

open scoped Nat
open AgohGiuga Finset

namespace OpenProofs.AgohGiuga

/-- `x` is `n`-integral: its denominator is coprime to `n`. -/
def AGNInt (n : ℕ) (x : ℚ) : Prop := Nat.Coprime x.den n

lemma agNInt_intCast (n : ℕ) (z : ℤ) : AGNInt n z := by
  simp [AGNInt]

lemma agNInt_natCast (n : ℕ) (z : ℕ) : AGNInt n z := by
  simp [AGNInt]

lemma agNInt_add {n : ℕ} {x y : ℚ} (hx : AGNInt n x) (hy : AGNInt n y) : AGNInt n (x + y) :=
  Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd x y) (Nat.Coprime.mul_left hx hy)

lemma agNInt_mul {n : ℕ} {x y : ℚ} (hx : AGNInt n x) (hy : AGNInt n y) : AGNInt n (x * y) :=
  Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd x y) (Nat.Coprime.mul_left hx hy)

lemma agNInt_neg {n : ℕ} {x : ℚ} (hx : AGNInt n x) : AGNInt n (-x) := by
  unfold AGNInt; rwa [Rat.den_neg_eq_den]

lemma agNInt_sub {n : ℕ} {x y : ℚ} (hx : AGNInt n x) (hy : AGNInt n y) : AGNInt n (x - y) := by
  rw [sub_eq_add_neg]; exact agNInt_add hx (agNInt_neg hy)

lemma agNInt_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, AGNInt n (f i)) :
    AGNInt n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using agNInt_intCast n 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact agNInt_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `x * d = m` with `n ∣ d`, then `n ∣ m * x.den`. -/
lemma agNInt_dvd {n : ℕ} {x : ℚ} {m d : ℤ} (hm : x * d = m) (hd : (n : ℤ) ∣ d) :
    (n : ℤ) ∣ m * x.den := by
  obtain ⟨d', rfl⟩ := hd
  refine ⟨x.num * d', ?_⟩
  have h1 := Rat.mul_den_eq_num x
  have : ((m * x.den : ℤ) : ℚ) = ((n * (x.num * d') : ℤ) : ℚ) := by
    push_cast
    rw [← hm, ← h1]
    push_cast
    ring
  exact_mod_cast this

lemma agNInt_div_iff {n : ℕ} (hn : n ≠ 0) (m : ℤ) : AGNInt n ((m : ℚ) / n) ↔ (n : ℤ) ∣ m := by
  constructor
  · intro h
    have h2 := agNInt_dvd (n := n) (x := (m : ℚ) / n) (m := m) (d := n) (by rw [Int.cast_natCast]; field_simp) dvd_rfl
    exact (Nat.isCoprime_iff_coprime.mpr h.symm).dvd_of_dvd_mul_right h2
  · rintro ⟨c, rfl⟩
    have : ((n * c : ℤ) : ℚ) / n = c := by push_cast; field_simp
    rw [this]; exact agNInt_intCast n c

/-- Weak von Staudt–Clausen: `n * B_{2m}` is `n`-integral. -/
lemma agNInt_mul_bernoulli_even {n : ℕ} (m : ℕ) : AGNInt n (n * bernoulli (2 * m)) := by
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
  set F := (range (2 * m + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * m
  have : (n : ℚ) * bernoulli (2 * m) = n * z - ∑ p ∈ F, (n : ℚ) * (1 / p) := by
    rw [hz, ← Finset.mul_sum]; ring
  rw [this]
  refine agNInt_sub (agNInt_mul (agNInt_natCast n n) (agNInt_intCast n z)) (agNInt_sum _ _ ?_)
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.mp hp).2.1
  by_cases hpn : p ∣ n
  · have : (n : ℚ) * (1 / p) = ((n / p : ℕ) : ℚ) := by
      rw [Nat.cast_div hpn (by exact_mod_cast hpp.ne_zero)]; ring
    rw [this]; exact agNInt_natCast n _
  · refine agNInt_mul (agNInt_natCast n n) ?_
    unfold AGNInt
    rw [show ((1 : ℚ) / p).den = p by simp [hpp.ne_zero]]
    exact (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpn

/-- For odd `n`, odd-index Bernoulli numbers are `n`-integral. -/
lemma agNInt_bernoulli_odd {n j : ℕ} (hn : Odd n) (hj : Odd j) : AGNInt n (bernoulli j) := by
  rcases Nat.lt_or_ge 1 j with h | h
  · rw [bernoulli_eq_zero_of_odd hj h]; exact agNInt_intCast n 0
  · obtain rfl : j = 1 := by obtain ⟨t, rfl⟩ := hj; omega
    rw [bernoulli_one]
    unfold AGNInt
    rw [show ((-1 : ℚ) / 2).den = 2 by norm_num]
    exact Nat.coprime_two_left.mpr hn

/-- Faulhaber's formula, split as `n * B_{n-1} + n * Y`. -/
lemma ag_faulhaber {n : ℕ} (hn : 2 ≤ n) :
    (∑ i ∈ range n, (i : ℚ) ^ (n - 1)) = n * bernoulli (n - 1) +
      n * ∑ j ∈ range (n - 1), bernoulli j * (n.choose j) * (n : ℚ) ^ (n - 2 - j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, sum_range_pow, Finset.sum_range_succ]
  rw [Nat.choose_succ_self_right, show m + 1 + 1 - (m + 1) = 1 by omega, add_comm, Finset.mul_sum]
  congr 1
  · push_cast
    field_simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    rw [show m + 1 + 1 - j = (m + 2 - 2 - j) + 2 by omega, pow_add]
    push_cast
    field_simp
    ring

lemma ag_sum_Ioo {R : Type*} [CommSemiring R] (n k : ℕ) (hk : k ≠ 0) :
    ((∑ i ∈ Ioo 0 n, i ^ k : ℕ) : R) = ∑ i ∈ range n, (i : R) ^ k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [Finset.range_eq_Ico, ← Finset.Ioo_insert_left hn, Finset.sum_insert (by simp)]
  push_cast
  simp [zero_pow hk]

/-- For even `n ≥ 4` Giuga's congruence fails: the power sum is `≡ -itself (mod n)`. -/
lemma ag_not_sum_even {n : ℕ} (hn : 4 ≤ n) (he : Even n) :
    ¬ n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) := by
  intro h
  have hk : Odd (n - 1) := by obtain ⟨t, rfl⟩ := he; exact ⟨t - 1, by omega⟩
  have h0 : ((1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [Nat.cast_add, Nat.cast_one, ag_sum_Ioo n (n - 1) (by omega)] at h0
  set T := ∑ i ∈ range n, (i : ZMod n) ^ (n - 1) with hT
  have h1 : ∑ j ∈ range n, ((n - 1 - j : ℕ) : ZMod n) ^ (n - 1) =
      -∑ j ∈ range n, ((j : ZMod n) + 1) ^ (n - 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    rw [← hk.neg_pow, Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
    congr 1
    push_cast
    ring
  have h2 : ∑ j ∈ range n, ((j : ZMod n) + 1) ^ (n - 1) = T := by
    have e1 := Finset.sum_range_succ' (fun j => (j : ZMod n) ^ (n - 1)) n
    have e2 := Finset.sum_range_succ (fun j => (j : ZMod n) ^ (n - 1)) n
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, ZMod.natCast_self,
      zero_pow (by omega : n - 1 ≠ 0), add_zero] at e1 e2
    rw [← e1, e2]
  have hTT : T = -T := by
    calc T = ∑ j ∈ range n, ((n - 1 - j : ℕ) : ZMod n) ^ (n - 1) :=
          (Finset.sum_range_reflect (fun j => (j : ZMod n) ^ (n - 1)) n).symm
      _ = -T := by rw [h1, h2]
  have h3 : ((2 : ℕ) : ZMod n) = 0 := by
    push_cast
    linear_combination 2 * h0 - hTT
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h3)
  omega

/-- The core equivalence: with `n * B` `n`-integral, Agoh's integer condition is
`n`-integrality of `1/n + B`. -/
lemma ag_congr_iff {n : ℕ} (hn : n ≠ 0) (B : ℚ) (hB : AGNInt n (n * B)) :
    (∃ k : ℤ, (n : ℤ) * B.num + B.den = k * (n : ℤ) ^ 2) ↔ AGNInt n (1 / n + B) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hD : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_ne_zero
  have key : B * B.den = B.num := Rat.mul_den_eq_num B
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨u, v, huv⟩ := Rat.isCoprime_num_den B
    have hc' : (n : ℚ) * B.num + B.den = c * (n : ℚ) ^ 2 := by exact_mod_cast hc
    have huv' : (u : ℚ) * B.num + v * B.den = 1 := by exact_mod_cast huv
    have h0 : (1 + n * B - c * u * n ^ 2 * B - c * v * n ^ 2) * B.den = 0 := by
      linear_combination n * key + hc' - c * n ^ 2 * huv' - c * u * n ^ 2 * key
    have h1 : 1 + n * B - c * u * n ^ 2 * B - c * v * n ^ 2 = 0 :=
      (mul_eq_zero.mp h0).resolve_right hD
    have : 1 / n + B = c * u * (n * B) + c * v * n := by
      field_simp
      linear_combination h1
    rw [this]
    exact agNInt_add (agNInt_mul (by exact_mod_cast agNInt_intCast n (c * u)) hB)
      (agNInt_mul (by exact_mod_cast agNInt_intCast n (c * v)) (agNInt_natCast n n))
  · intro h
    have hxM : (1 / n + B) * (((n : ℤ) * B.den : ℤ) : ℚ) = ((B.den + n * B.num : ℤ) : ℚ) := by
      push_cast
      field_simp
      linear_combination n * key
    have hcop : IsCoprime (n : ℤ) ((1 / n + B).den : ℤ) := Nat.isCoprime_iff_coprime.mpr h.symm
    obtain ⟨M₁, hM₁⟩ := hcop.dvd_of_dvd_mul_right (agNInt_dvd hxM (dvd_mul_right _ _))
    have hxD : (1 / n + B) * ((B.den : ℤ) : ℚ) = (M₁ : ℚ) := by
      have hM₁' : (B.den : ℚ) + n * B.num = n * M₁ := by exact_mod_cast hM₁
      push_cast
      refine mul_left_cancel₀ hn' ?_
      field_simp
      linear_combination n * key + hM₁'
    have hDn : (n : ℤ) ∣ (B.den : ℤ) := ⟨M₁ - B.num, by linear_combination hM₁⟩
    obtain ⟨M₂, hM₂⟩ := hcop.dvd_of_dvd_mul_right (agNInt_dvd hxD hDn)
    exact ⟨M₂, by linear_combination hM₁ + (n : ℤ) * hM₂⟩

lemma ag_odd {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    (∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + (bernoulli' (n - 1)).den = k * (n : ℤ) ^ 2) ↔
      n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by omega : n - 1 ≠ 1)]
  have hn0 : n ≠ 0 := by omega
  obtain ⟨t, ht⟩ : Even (n - 1) := by obtain ⟨s, rfl⟩ := ho; exact ⟨s, by omega⟩
  have hB : AGNInt n (n * bernoulli (n - 1)) := by
    rw [ht, ← two_mul]; exact agNInt_mul_bernoulli_even t
  rw [ag_congr_iff hn0 _ hB, ← Int.natCast_dvd_natCast, ← agNInt_div_iff hn0]
  set Y := ∑ j ∈ range (n - 1), bernoulli j * (n.choose j) * (n : ℚ) ^ (n - 2 - j) with hYdef
  have hY : AGNInt n Y := by
    refine agNInt_sum _ _ fun j hj => ?_
    have hj := Finset.mem_range.mp hj
    rcases Nat.even_or_odd j with hje | hjo
    · have hj3 : j ≤ n - 3 := by
        obtain ⟨a, rfl⟩ := hje; obtain ⟨s, rfl⟩ := ho; omega
      have : bernoulli j * (n.choose j) * (n : ℚ) ^ (n - 2 - j) =
          (n * bernoulli j) * (n.choose j) * (n : ℚ) ^ (n - 3 - j) := by
        rw [show n - 2 - j = (n - 3 - j) + 1 by omega, pow_succ]; ring
      rw [this]
      obtain ⟨a, rfl⟩ := hje
      rw [← two_mul]
      refine agNInt_mul (agNInt_mul (agNInt_mul_bernoulli_even a) (agNInt_natCast n _)) ?_
      exact_mod_cast agNInt_natCast n (n ^ (n - 3 - (a + a)))
    · refine agNInt_mul (agNInt_mul (agNInt_bernoulli_odd ho hjo) (agNInt_natCast n _)) ?_
      exact_mod_cast agNInt_natCast n (n ^ (n - 2 - j))
  have hsum : (((1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) : ℕ) : ℤ) : ℚ) / n =
      (1 / n + bernoulli (n - 1)) + Y := by
    rw [Int.cast_natCast, Nat.cast_add, Nat.cast_one, ag_sum_Ioo n (n - 1) (by omega),
      ag_faulhaber (by omega), ← hYdef]
    field_simp
    ring
  rw [hsum]
  constructor
  · intro h; exact agNInt_add h hY
  · intro h; simpa using agNInt_sub h hY

lemma ag_pointwise (n : ℕ) (hn : 2 ≤ n) :
    (∃ k : ℤ, (n : ℤ) * (bernoulli' (n - 1)).num + (bernoulli' (n - 1)).den = k * (n : ℤ) ^ 2) ↔
      n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) := by
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · refine iff_of_true ⟨1, ?_⟩ (by decide)
    rw [show 2 - 1 = 1 by rfl, bernoulli'_one]
    norm_num
  · rcases Nat.even_or_odd n with he | ho
    · have h4 : 4 ≤ n := by obtain ⟨t, rfl⟩ := he; omega
      refine iff_of_false ?_ (ag_not_sum_even h4 he)
      rintro ⟨k, hk⟩
      rw [bernoulli'_eq_zero_of_odd (by obtain ⟨t, rfl⟩ := he; exact ⟨t - 1, by omega⟩)
        (by omega)] at hk
      simp only [Rat.num_zero, mul_zero, Rat.den_zero, Nat.cast_one, zero_add] at hk
      have h16 : (16 : ℤ) ≤ (n : ℤ) ^ 2 := by
        have : (4 : ℤ) ≤ n := by exact_mod_cast h4
        nlinarith
      rcases le_or_gt k 0 with hk0 | hk0 <;> nlinarith
    · exact ag_odd h3 ho

end OpenProofs.AgohGiuga

namespace OpenProofs.AgohGiuga

theorem agoh_giuga.variants.equivalence : AgohGiugaCongr ↔ AgohGiugaSum := by
  unfold AgohGiugaCongr AgohGiugaSum
  exact forall_congr' fun p => forall_congr' fun hp => iff_congr Iff.rfl (ag_pointwise p hp)

end OpenProofs.AgohGiuga
