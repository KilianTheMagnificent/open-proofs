import FormalConjectures.ErdosProblems.«287»

/-!
# `Erdos287.erdos_287.variants.prime_conjecture_implies`

Upstream: `Erdos287.erdos_287.variants.prime_conjecture_implies` (category textbook), `FormalConjectures/ErdosProblems/287.lean` line 108.
Proof idea: suppose all gaps are at most 2, with first term `a` and last term `b`.
Then `b ≥ a + k - 1`, and `b ≥ 2a + 3` (otherwise all terms lie in `[a, 2a+2]`, whose
reciprocal sum is `< 1` for `a ≥ 16`; small `a` is handled by `b ≥ k - 1`). Apply the
prime conjecture with `N = (b-1)/2`: we get primes `p ∈ [N, 2N] ⊆ (a, b)` and `q = (p+1)/2`.
If `p` is a term, take `r = p`; otherwise the gap condition forces `p + 1 = 2q` to be a term,
take `r = q`. In both cases `r > 300`, `6r > b` and `r` divides some term. Splitting the sum
into terms divisible by `r` (each `r·j`, `j ≤ 5`, summing to `C/(60r)` with `0 < C ≤ 300`)
and the rest (summing to `A/B` with `r ∤ B`) gives `r ∣ C·B`, a contradiction.
-/

open Erdos287

namespace OpenProofs.Erdos287

/-- Divisibility obstruction: a prime `r > 300` with `6r > max S` dividing some element of
`S` prevents `∑_{n ∈ S} 1/n = 1`. -/
theorem erdos287PcCore (S : Finset ℕ) (b r : ℕ) (hpos : ∀ n ∈ S, 0 < n)
    (hle : ∀ n ∈ S, n ≤ b) (hsum : ∑ n ∈ S, (1:ℝ) / n = 1) (hr : r.Prime)
    (hrb : b < 6 * r) (hr300 : 300 < r) (hex : ∃ n ∈ S, r ∣ n) : False := by
  classical
  set S₁ := S.filter (fun n => ¬ r ∣ n) with hS₁
  set S₂ := S.filter (fun n => r ∣ n) with hS₂
  have hsplit : ∑ n ∈ S₂, (1:ℝ) / n + ∑ n ∈ S₁, (1:ℝ) / n = 1 := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun n => r ∣ n) (fun n => (1:ℝ) / n)).trans hsum
  have hr0 : 0 < r := hr.pos
  have hr0' : (r:ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hS₂mem : ∀ n ∈ S₂, ∃ j, n = r * j ∧ 1 ≤ j ∧ j ≤ 5 := by
    intro n hn
    rw [hS₂, Finset.mem_filter] at hn
    obtain ⟨hnS, j, rfl⟩ := hn
    refine ⟨j, rfl, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        have := hpos _ hnS
        simp at this
      · exact h
    · by_contra h
      have h1 := hle _ hnS
      have h2 : r * 6 ≤ r * j := Nat.mul_le_mul_left r (by omega)
      omega
  have hdvd60 : ∀ n ∈ S₂, n ∣ 60 * r := by
    intro n hn
    obtain ⟨j, rfl, h1, h5⟩ := hS₂mem n hn
    have : j ∣ 60 := by interval_cases j <;> norm_num
    rw [mul_comm 60 r]
    exact Nat.mul_dvd_mul_left r this
  have hS₂pos : ∀ n ∈ S₂, 0 < n := fun n hn => hpos n (Finset.mem_of_mem_filter n hn)
  have hS₁pos : ∀ n ∈ S₁, 0 < n := fun n hn => hpos n (Finset.mem_of_mem_filter n hn)
  set C := ∑ n ∈ S₂, 60 * r / n with hC
  have hCreal : ∑ n ∈ S₂, (1:ℝ) / n = (C : ℝ) / (60 * r) := by
    rw [hC, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (hS₂pos n hn).ne'
    rw [Nat.cast_div (hdvd60 n hn) hn0]
    push_cast
    field_simp
  set B := ∏ n ∈ S₁, n with hB
  have hBpos : 0 < B := Finset.prod_pos hS₁pos
  have hB0 : (B:ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
  set A := ∑ n ∈ S₁, B / n with hA
  have hAreal : ∑ n ∈ S₁, (1:ℝ) / n = (A : ℝ) / B := by
    rw [hA, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (hS₁pos n hn).ne'
    rw [Nat.cast_div (show n ∣ B from Finset.dvd_prod_of_mem _ hn) hn0]
    field_simp
  have h60 : (60 * (r:ℝ)) ≠ 0 := by positivity
  have keyR : (C:ℝ) * B + A * (60 * r) = B * (60 * r) := by
    rw [hCreal, hAreal, div_add_div _ _ h60 hB0, div_eq_one_iff_eq (mul_ne_zero h60 hB0)]
      at hsplit
    linarith
  have keyN : C * B + A * (60 * r) = B * (60 * r) := by exact_mod_cast keyR
  have h1 : r ∣ B * (60 * r) := dvd_mul_of_dvd_right (dvd_mul_left r 60) B
  have h2 : r ∣ A * (60 * r) := dvd_mul_of_dvd_right (dvd_mul_left r 60) A
  have h3 : r ∣ C * B := by
    rw [← keyN] at h1
    exact (Nat.dvd_add_left h2).mp h1
  rcases (Nat.Prime.dvd_mul hr).mp h3 with hc | hb
  · obtain ⟨n, hnS, hrn⟩ := hex
    have hnS₂ : n ∈ S₂ := by rw [hS₂, Finset.mem_filter]; exact ⟨hnS, hrn⟩
    have hCpos : 0 < C := by
      have hterm : 0 < 60 * r / n :=
        Nat.div_pos (by have := hle n hnS; omega) (hS₂pos n hnS₂)
      exact lt_of_lt_of_le hterm (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnS₂)
    have hcard : S₂.card ≤ 5 := by
      have hsub : S₂ ⊆ (Finset.Icc 1 5).image (fun j => r * j) := by
        intro n hn
        obtain ⟨j, rfl, h1, h5⟩ := hS₂mem n hn
        exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨h1, h5⟩, rfl⟩
      calc S₂.card ≤ ((Finset.Icc 1 5).image (fun j => r * j)).card := Finset.card_le_card hsub
        _ ≤ (Finset.Icc 1 5).card := Finset.card_image_le
        _ = 5 := by simp
    have hterm : ∀ n ∈ S₂, 60 * r / n ≤ 60 := by
      intro n hn
      obtain ⟨j, rfl, h1, h5⟩ := hS₂mem n hn
      rw [mul_comm 60 r, Nat.mul_div_mul_left 60 j hr0]
      exact Nat.div_le_self 60 j
    have hC300 : C ≤ 300 :=
      calc C ≤ ∑ _n ∈ S₂, 60 := Finset.sum_le_sum hterm
        _ = S₂.card * 60 := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 300 := by omega
    have := Nat.le_of_dvd hCpos hc
    omega
  · rw [hB] at hb
    obtain ⟨n, hn, hrn⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hb
    rw [hS₁, Finset.mem_filter] at hn
    exact hn.2 hrn

/-- With gaps at most 2, a skipped value strictly between the first and last term is
followed by a term. -/
theorem erdos287PcGap (k : ℕ) (s : Fin k → ℕ) (hs : StrictMono s) (hk : 2 ≤ k)
    (hgap : ∀ i : Fin (k - 1), s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩ ≤ 2)
    (m : ℕ) (h1 : s ⟨0, by omega⟩ < m) (h2 : m < s ⟨k - 1, by omega⟩)
    (hm : ∀ i, s i ≠ m) : ∃ i, s i = m + 1 := by
  have key : ∀ j (hj : j < k), s ⟨j, hj⟩ < m ∨ ∃ i, s i = m + 1 := by
    intro j
    induction j with
    | zero => intro hj; left; exact h1
    | succ j ih =>
      intro hj
      rcases ih (by omega) with h | h
      · have hg := hgap ⟨j, by omega⟩
        have hlt : s ⟨j, by omega⟩ < s ⟨j + 1, hj⟩ := hs (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
        have hne := hm ⟨j + 1, hj⟩
        simp only at hg
        by_cases hc : s ⟨j + 1, hj⟩ < m
        · left; exact hc
        · right; exact ⟨⟨j + 1, hj⟩, by omega⟩
      · right; exact h
  rcases key (k - 1) (by omega) with h | h
  · omega
  · exact h

theorem erdos287PcLower (k : ℕ) (s : Fin k → ℕ) (hs : StrictMono s) :
    ∀ j (hj : j < k), s ⟨0, by omega⟩ + j ≤ s ⟨j, hj⟩ := by
  intro j
  induction j with
  | zero => intro hj; simp
  | succ j ih =>
    intro hj
    have := ih (by omega)
    have hlt : s ⟨j, by omega⟩ < s ⟨j + 1, hj⟩ := hs (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
    omega

theorem erdos287PcHarm (a : ℕ) (ha : 16 ≤ a) :
    ∑ n ∈ Finset.Icc a (2 * a + 2), (1:ℝ) / n < 1 := by
  set m := a / 2 with hm
  have hm1 : 2 * m ≤ a := by omega
  have hm2 : a ≤ 2 * m + 1 := by omega
  have ha' : (16:ℝ) ≤ a := by exact_mod_cast ha
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hIcc : Finset.Icc a (2 * a + 2) = Finset.Ico a (2 * a + 3) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, ← Finset.sum_Ico_consecutive _ (show a ≤ a + m by omega)
    (show a + m ≤ 2 * a + 3 by omega)]
  have hA : ∑ n ∈ Finset.Ico a (a + m), (1:ℝ) / n ≤ (m:ℝ) * (1 / a) := by
    have h := Finset.sum_le_card_nsmul (Finset.Ico a (a + m)) (fun n => (1:ℝ) / n) (1 / (a:ℝ)) ?_
    · rw [Nat.card_Ico, nsmul_eq_mul] at h
      have hc : (((a + m - a) : ℕ) : ℝ) = (m:ℝ) := by rw [Nat.add_sub_cancel_left]
      rw [hc] at h; exact h
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      apply one_div_le_one_div_of_le (by linarith)
      exact_mod_cast hn.1
  have hB : ∑ n ∈ Finset.Ico (a + m) (2 * a + 3), (1:ℝ) / n
      ≤ ((a:ℝ) + 3 - m) * (1 / ((a:ℝ) + m)) := by
    have h := Finset.sum_le_card_nsmul (Finset.Ico (a + m) (2 * a + 3)) (fun n => (1:ℝ) / n)
      (1 / ((a:ℝ) + m)) ?_
    · rw [Nat.card_Ico, nsmul_eq_mul] at h
      have hc : (((2 * a + 3 - (a + m)) : ℕ) : ℝ) = (a:ℝ) + 3 - m := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hc] at h; exact h
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      apply one_div_le_one_div_of_le (by linarith)
      exact_mod_cast hn.1
  have hfin : (m:ℝ) * (1 / a) + ((a:ℝ) + 3 - m) * (1 / ((a:ℝ) + m)) < 1 := by
    have hm1' : 2 * (m:ℝ) ≤ a := by exact_mod_cast hm1
    have hm2' : (a:ℝ) ≤ 2 * m + 1 := by exact_mod_cast hm2
    have hapos : (0:ℝ) < a := by linarith
    have hampos : (0:ℝ) < a + m := by linarith
    rw [mul_one_div, mul_one_div, div_add_div _ _ hapos.ne' hampos.ne',
      div_lt_one (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1') (show (0:ℝ) ≤ m - 3 by linarith)]
  linarith

theorem erdos_287.variants.prime_conjecture_implies : type_of% erdos_287.variants.prime_conjecture →
    ∃ (k₀ : ℕ), ∀ᵉ (k : ℕ) (hk₀ : k₀ ≤ k) (hk : 2 ≤ k) (s : Fin k → ℕ),
      StrictMono s → 1 < s ⟨0, by omega⟩ →
      ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
      3 ≤ max_gap k s := by
  intro hpc
  obtain ⟨N₀, hN₀⟩ := hpc
  refine ⟨2 * N₀ + 1300, ?_⟩
  intro k hk₀ hk s hs hs0 hsum
  by_contra hlt
  have hmg : max_gap k s ≤ 2 := by omega
  have hgap : ∀ i : Fin (k - 1), s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩ ≤ 2 := by
    intro i
    exact le_trans (Finset.le_sup (f := fun i : Fin (k - 1) =>
      s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩) (Finset.mem_univ i)) hmg
  set a := s ⟨0, by omega⟩ with ha
  set b := s ⟨k - 1, by omega⟩ with hb
  have hab : a + (k - 1) ≤ b := erdos287PcLower k s hs (k - 1) (by omega)
  set S := Finset.univ.image s with hS
  have hSsum : ∑ n ∈ S, (1:ℝ) / n = 1 := by
    rw [hS, Finset.sum_image (fun x _ y _ h => hs.injective h)]; exact hsum
  have hSmem : ∀ n ∈ S, a ≤ n ∧ n ≤ b := by
    intro n hn
    rw [hS, Finset.mem_image] at hn
    obtain ⟨i, _, rfl⟩ := hn
    constructor
    · exact hs.monotone (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    · exact hs.monotone (Fin.le_iff_val_le_val.mpr (by have := i.isLt; simp only; omega))
  have hb2a : 2 * a + 3 ≤ b := by
    by_contra hcon
    by_cases ha20 : a ≤ 20
    · omega
    · have hsub : S ⊆ Finset.Icc a (2 * a + 2) := by
        intro n hn; have := hSmem n hn; rw [Finset.mem_Icc]; omega
      have h1 : ∑ n ∈ S, (1:ℝ) / n ≤ ∑ n ∈ Finset.Icc a (2 * a + 2), (1:ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      have h2 := erdos287PcHarm a (by omega)
      linarith
  obtain ⟨p, hp, hpN, hp2N, hq⟩ := hN₀ ((b - 1) / 2) (by omega)
  have hpa : a < p := by omega
  have hpb : p < b := by omega
  have hSpos : ∀ n ∈ S, 0 < n := fun n hn => by have := hSmem n hn; omega
  have hSle : ∀ n ∈ S, n ≤ b := fun n hn => (hSmem n hn).2
  by_cases hpS : p ∈ S
  · exact erdos287PcCore S b p hSpos hSle hSsum hp (by omega) (by omega) ⟨p, hpS, dvd_rfl⟩
  · have hm : ∀ i, s i ≠ p := fun i hi =>
      hpS (by rw [hS, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, hi⟩)
    obtain ⟨i, hi⟩ := erdos287PcGap k s hs hk hgap p hpa hpb hm
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    refine erdos287PcCore S b ((p + 1) / 2) hSpos hSle hSsum hq (by omega) (by omega)
      ⟨p + 1, ?_, ⟨2, by omega⟩⟩
    rw [hS, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, hi⟩

end OpenProofs.Erdos287
