import FormalConjectures.ErdosProblems.«692»

/-!
# Erdős 692 (ii): no `n`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos692.erdos_692.parts.ii.no_constant_answer`.

Upstream `Erdos692.erdos_692.parts.ii (n : ℕ)` asserts, for every `n` and every density function
`δ`, that `δ n erdos_692.parts.ii.answer` is the largest value of `δ n m` over `m > n + 1`. Take
`n = m₀`. The interval `(m₀, m₀)` is empty, so `δ₁(m₀, m₀) = 0`; but `δ₁(m₀, m₀ + 2)` is the density
of the multiples of `m₀ + 1`, which is positive. To make the hypothesis on `δ` non-vacuous we
exhibit a `δ` with `IsDelta₁ a b (δ a b)` for all `a, b`: each set `exactlyOneDivisorIn a b` is
periodic with period `b!`, and a periodic set has a natural density.
-/

open Erdos692 Filter

namespace OpenProofs.Erdos692

open scoped Classical in
theorem count_add_period_aux692 (p : ℕ → Prop) (L : ℕ) (hp : ∀ x, p (x + L) ↔ p x) (b : ℕ) :
    Nat.count p (b + L) = Nat.count p b + Nat.count p L := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show b + 1 + L = (b + L) + 1 by omega, Nat.count_succ, Nat.count_succ, ih]
    have := hp b
    by_cases hb : p b
    · rw [if_pos (this.2 hb), if_pos hb]; ring
    · rw [if_neg (fun h => hb (this.1 h)), if_neg hb]; ring

open scoped Classical in
theorem count_mul_period_aux692 (p : ℕ → Prop) (L : ℕ) (hp : ∀ x, p (x + L) ↔ p x) (q r : ℕ) :
    Nat.count p (q * L + r) = q * Nat.count p L + Nat.count p r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * L + r = (q * L + r) + L by ring, count_add_period_aux692 p L hp, ih]
    ring

open scoped Classical in
/-- A periodic set of naturals has a natural density. -/
theorem hasDensity_of_periodic_aux692 (S : Set ℕ) (L : ℕ) (hL : 0 < L)
    (hS : ∀ x, x + L ∈ S ↔ x ∈ S) :
    S.HasDensity ((Nat.count (· ∈ S) L : ℝ) / L) := by
  set c := Nat.count (· ∈ S) L with hc
  have hncard : ∀ b : ℕ, ((S ∩ Set.univ) ∩ Set.Iio b).ncard = Nat.count (· ∈ S) b := by
    intro b
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [and_comm]
  have huniv : ∀ b : ℕ, (Set.univ ∩ Set.Iio b).ncard = b := by
    intro b
    simp [Set.ncard_eq_toFinset_card']
  unfold Set.HasDensity
  simp only [Set.partialDensity, hncard, huniv]
  -- error term is bounded by `2 L`
  have hbound : ∀ b : ℕ, |(Nat.count (· ∈ S) b : ℝ) - b * c / L| ≤ 2 * L := by
    intro b
    have hb : b = (b / L) * L + b % L := (Nat.div_add_mod' b L).symm
    have hcnt := count_mul_period_aux692 (· ∈ S) L hS (b / L) (b % L)
    rw [← hb] at hcnt
    have hr : b % L < L := Nat.mod_lt _ hL
    have hcr : Nat.count (· ∈ S) (b % L) ≤ b % L := Nat.count_le _
    have hcL : c ≤ L := Nat.count_le _
    have hLr : (L : ℝ) ≠ 0 := by positivity
    have e : (b : ℝ) * c / L = (b / L : ℕ) * c + (b % L : ℕ) * c / L := by
      conv_lhs => rw [hb]
      push_cast
      field_simp
    rw [hcnt, e]
    push_cast
    have h1 : ((b % L : ℕ) : ℝ) * c / L ≤ c := by
      rw [div_le_iff₀ (by positivity)]
      have : ((b % L : ℕ) : ℝ) ≤ L := by exact_mod_cast hr.le
      nlinarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)]
    have h2 : (0 : ℝ) ≤ ((b % L : ℕ) : ℝ) * c / L := by positivity
    have h3 : ((Nat.count (· ∈ S) (b % L) : ℕ) : ℝ) ≤ L := by exact_mod_cast (hcr.trans hr.le)
    have h4 : (c : ℝ) ≤ L := by exact_mod_cast hcL
    rw [abs_le]
    constructor <;> nlinarith [(Nat.cast_nonneg (Nat.count (· ∈ S) (b % L)) : (0:ℝ) ≤ _)]
  have hlim : Tendsto (fun b : ℕ => ((Nat.count (· ∈ S) b : ℝ) - b * c / L) / b) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun b : ℕ => 2 * (L : ℝ) / b)
    · filter_upwards [eventually_gt_atTop 0] with b hb
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hb : (0 : ℝ) < b)]
      exact div_le_div_of_nonneg_right (hbound b) (by positivity)
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  have := hlim.const_add ((c : ℝ) / L)
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  ring


theorem exactlyOne_periodic_aux692 (a b x : ℕ) :
    x + b.factorial ∈ exactlyOneDivisorIn a b ↔ x ∈ exactlyOneDivisorIn a b := by
  have : {d ∈ Set.Ioo a b | d ∣ x + b.factorial} = {d ∈ Set.Ioo a b | d ∣ x} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (Nat.dvd_add_left (Nat.dvd_factorial (by omega) h2.le)).1 h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (Nat.dvd_add_left (Nat.dvd_factorial (by omega) h2.le)).2 h3⟩
  simp only [exactlyOneDivisorIn, Set.mem_ofPred_eq, this]

open scoped Classical in
theorem erdos_692.parts.ii.no_constant_answer :
    ∀ m₀ : ℕ, ¬ ∀ (n : ℕ), ∀ δ : ℕ → ℕ → ℝ, (∀ a b, IsDelta₁ a b (δ a b)) →
      IsGreatest (δ n '' Set.Ioi (n + 1)) (δ n m₀) := by
  intro m₀ h
  let δ : ℕ → ℕ → ℝ := fun a b =>
    (Nat.count (· ∈ exactlyOneDivisorIn a b) b.factorial : ℝ) / b.factorial
  have hδ : ∀ a b, IsDelta₁ a b (δ a b) := fun a b =>
    hasDensity_of_periodic_aux692 _ _ (Nat.factorial_pos b) (exactlyOne_periodic_aux692 a b)
  have hle := (h m₀ δ hδ).2 ⟨m₀ + 2, by simp, rfl⟩
  have h0 : δ m₀ m₀ = 0 := by
    have : exactlyOneDivisorIn m₀ m₀ = ∅ := by
      ext x
      simp [exactlyOneDivisorIn]
    simp only [δ, this]
    simp
  have hpos : 0 < δ m₀ (m₀ + 2) := by
    have hmem : 0 ∈ exactlyOneDivisorIn m₀ (m₀ + 2) := by
      have : {d ∈ Set.Ioo m₀ (m₀ + 2) | d ∣ 0} = {m₀ + 1} := by
        ext d
        simp only [Set.mem_ofPred_eq, Set.mem_Ioo, dvd_zero, and_true, Set.mem_singleton_iff]
        omega
      show {d ∈ Set.Ioo m₀ (m₀ + 2) | d ∣ 0}.ncard = 1
      rw [this, Set.ncard_singleton]
    have hc : 1 ≤ Nat.count (· ∈ exactlyOneDivisorIn m₀ (m₀ + 2)) (m₀ + 2).factorial := by
      have h1 : Nat.count (· ∈ exactlyOneDivisorIn m₀ (m₀ + 2)) 1 = 1 := by
        simp [Nat.count_succ, hmem]
      rw [← h1]
      exact Nat.count_monotone _ (Nat.factorial_pos _)
    simp only [δ]
    have : (1 : ℝ) ≤ Nat.count (· ∈ exactlyOneDivisorIn m₀ (m₀ + 2)) (m₀ + 2).factorial := by
      exact_mod_cast hc
    have : (0 : ℝ) < (m₀ + 2).factorial := by exact_mod_cast Nat.factorial_pos _
    positivity
  linarith

end OpenProofs.Erdos692
