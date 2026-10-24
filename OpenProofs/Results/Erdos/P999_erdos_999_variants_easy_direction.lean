import FormalConjectures.ErdosProblems.«999»

/-!
# `Erdos999.erdos_999.variants.easy_direction`

Upstream: `Erdos999.erdos_999.variants.easy_direction` (category textbook), `FormalConjectures/ErdosProblems/999.lean` line 63.
Proof idea: first Borel–Cantelli lemma on `[1, 2]`. If the series were summable, let `S q` be
the points of `[1, 2]` within `f q / q` of some reduced fraction `p / q`. For `q ≥ 1` either
`f q / q ≥ 1/2`, so `vol (S q) ≤ 1 ≤ 6 φ(q) f(q) / q`, or `p / q ∈ (1/2, 5/2)`, so `p = r + k q`
with `r < q` coprime to `q` and `k < 3`, giving `vol (S q) ≤ 3 φ(q) · 2 f(q) / q`. Hence
`∑ vol (S q) < ∞`, so almost no point of `[1, 2]` lies in infinitely many `S q`; but almost every
point is approximable, which would force `vol [1, 2] = 0`.
-/

open MeasureTheory
open Erdos999

namespace OpenProofs.Erdos999

theorem erdos_999.variants.easy_direction (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q)
    (h : ∀ᵐ x : ℝ, IsApproximable f x) :
    ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q := by
  intro hsum
  let P : ℕ → ℝ → Prop := fun q x =>
    x ∈ Set.Icc (1:ℝ) 2 ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q
  have hbound : ∀ q, volume {x | P q x} ≤
      ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) := by
    intro q
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · have hempty : {x | P 0 x} = ∅ := by
        ext x
        simp only [P, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, p, -, hlt⟩
        rw [Nat.cast_zero, div_zero, div_zero] at hlt
        exact absurd hlt (not_lt.mpr (abs_nonneg _))
      rw [hempty, measure_empty]
      exact zero_le
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq
    have htot : (1:ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
    have hδ0 : 0 ≤ f q / q := div_nonneg (hf q) hqpos.le
    have hrw : (Nat.totient q : ℝ) * f q / q = Nat.totient q * (f q / q) := by ring
    by_cases hδ : (1:ℝ) / 2 ≤ f q / q
    · calc volume {x | P q x} ≤ volume (Set.Icc (1:ℝ) 2) := measure_mono (fun x hx => hx.1)
        _ = ENNReal.ofReal 1 := by rw [Real.volume_Icc]; norm_num
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hrw]
          nlinarith
    · push Not at hδ
      let T := ((Finset.range q).filter (q.Coprime)) ×ˢ Finset.range 3
      have hsub : {x | P q x} ⊆
          ⋃ rk ∈ T, Metric.ball (((rk.1 + rk.2 * q : ℕ) : ℝ) / q) (f q / q) := by
        rintro x ⟨hx, p, hpq, hlt⟩
        have habs := abs_lt.mp hlt
        have e : (p:ℝ) / q * q = p := div_mul_cancel₀ _ (ne_of_gt hqpos)
        have h1 : (q:ℝ) < 2 * p := by
          have h' : (1:ℝ) / 2 < p / q := by linarith [hx.1]
          have := mul_lt_mul_of_pos_right h' hqpos
          rw [e] at this
          linarith
        have h2 : 2 * (p:ℝ) < 5 * q := by
          have h' : (p:ℝ) / q < 5 / 2 := by linarith [hx.2]
          have := mul_lt_mul_of_pos_right h' hqpos
          rw [e] at this
          linarith
        have h1' : (q:ℤ) < 2 * p := by exact_mod_cast h1
        have h2' : 2 * p < 5 * (q:ℤ) := by exact_mod_cast h2
        set n := p.toNat with hn_def
        have hn : (n:ℤ) = p := Int.toNat_of_nonneg (by omega)
        have hnR : (n:ℝ) = p := by exact_mod_cast hn
        have hcop : Nat.Coprime n q := by
          rw [← hn, Int.gcd_natCast_natCast] at hpq
          exact hpq
        refine Set.mem_biUnion (x := (n % q, n / q)) ?_ ?_
        · refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩, Finset.mem_range.mpr ?_⟩
          · have : Nat.gcd q (n % q) = 1 := by
              rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
              exact hcop
            exact this
          · exact (Nat.div_lt_iff_lt_mul hq).mpr (by omega)
        · rw [Metric.mem_ball, Real.dist_eq, Nat.mod_add_div', hnR]
          exact hlt
      calc volume {x | P q x}
          ≤ volume (⋃ rk ∈ T, Metric.ball (((rk.1 + rk.2 * q : ℕ) : ℝ) / q) (f q / q)) :=
            measure_mono hsub
        _ ≤ ∑ rk ∈ T, volume (Metric.ball (((rk.1 + rk.2 * q : ℕ) : ℝ) / q) (f q / q)) :=
            measure_biUnion_finset_le _ _
        _ = ∑ rk ∈ T, ENNReal.ofReal (2 * (f q / q)) := by simp only [Real.volume_ball]
        _ = (T.card : ENNReal) * ENNReal.ofReal (2 * (f q / q)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ENNReal.ofReal (6 * ((Nat.totient q : ℝ) * f q / q)) := by
            have hc : T.card = Nat.totient q * 3 := by
              simp only [T, Finset.card_product, Finset.card_range, Nat.totient_eq_card_coprime]
            rw [hc, show (6 * ((Nat.totient q : ℝ) * f q / q)) =
                ((Nat.totient q * 3 : ℕ) : ℝ) * (2 * (f q / q)) by push_cast; ring,
              ENNReal.ofReal_mul (p := ((Nat.totient q * 3 : ℕ) : ℝ)) (by positivity),
              ENNReal.ofReal_natCast]
  have hfin : ∑' q, volume {x | P q x} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · exact ENNReal.ofReal_ne_top
    · intro q
      have := hf q
      positivity
    · exact hsum.mul_left 6
  have hzero := measure_setOfPred_frequently_eq_zero hfin
  have hnull : volume {x : ℝ | ¬ IsApproximable f x} = 0 := ae_iff.mp h
  have hsub : Set.Icc (1:ℝ) 2 ⊆
      {x | ∃ᶠ q in Filter.atTop, P q x} ∪ {x | ¬ IsApproximable f x} := by
    intro x hx
    by_cases hA : IsApproximable f x
    · left
      have := Nat.frequently_atTop_iff_infinite.mpr hA
      exact this.mono fun q hq => ⟨hx, hq.2⟩
    · right
      exact hA
  have hIcc : volume (Set.Icc (1:ℝ) 2) = 0 := by
    apply le_antisymm _ zero_le
    calc volume (Set.Icc (1:ℝ) 2) ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ = 0 := by rw [hzero, hnull, add_zero]
  rw [Real.volume_Icc] at hIcc
  norm_num at hIcc

end OpenProofs.Erdos999
