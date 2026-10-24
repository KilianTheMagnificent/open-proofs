import FormalConjectures.ErdosProblems.«295»

/-!
# `Erdos295.exists_k`

Upstream: `Erdos295.exists_k` (category textbook), `FormalConjectures/ErdosProblems/295.lean` line 37.
Proof idea: let `A = N + 2` and take the longest block `A, A+1, …, A+K-1` whose reciprocal sum
`f K` is at most `1` (it exists because `f (3A) > 1`). The remainder `r = 1 - f K` satisfies
`0 ≤ r < 1/(A+K)`, so the greedy (Fibonacci–Sylvester) algorithm writes `r` as a sum of
distinct unit fractions with denominators `> A+K` (each step strictly lowers the numerator).
The union of the block and the greedy denominators, listed in increasing order, is the sequence.
-/

open scoped Real
open Erdos295

namespace OpenProofs.Erdos295

/-- Greedy Egyptian-fraction expansion: if `p / q < 1 / M`, then `p / q` is a sum of distinct
unit fractions whose denominators all exceed `M`. -/
theorem egyptGreedyNat (p : ℕ) : ∀ (q M : ℕ), 0 < M → p * M < q →
    ∃ S : Finset ℕ, (∀ s ∈ S, M < s) ∧ ∑ s ∈ S, (1 / (s : ℚ)) = p / q := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro q M hM hpq
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨∅, by simp, by simp⟩
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hpq
  have hex : ∃ d, q ≤ p * d := ⟨q, Nat.le_mul_of_pos_left q hp⟩
  obtain ⟨d, hd1, hdmin⟩ : ∃ d, q ≤ p * d ∧ ∀ e < d, ¬ q ≤ p * e :=
    ⟨Nat.find hex, Nat.find_spec hex, fun e he => Nat.find_min hex he⟩
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h] at hd1; omega
    · exact h
  have hd2 : p * d < q + p := by
    obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have h1 := hdmin e (by omega)
    subst he
    rw [Nat.mul_succ]; omega
  have hMd : M < d := Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le hpq hd1)
  have hpq' : p < q := lt_of_le_of_lt (Nat.le_mul_of_pos_right p hM) hpq
  have hlt : p * d - q < p := by omega
  obtain ⟨S, hS1, hS2⟩ := ih (p * d - q) hlt (q * d) d hd0
    (Nat.mul_lt_mul_of_pos_right (by omega) hd0)
  refine ⟨insert d S, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hMd
    · exact lt_trans hMd (hS1 s hs)
  · rw [Finset.sum_insert (fun h => lt_irrefl d (hS1 d h)), hS2, Nat.cast_sub hd1]
    have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
    push_cast
    field_simp
    ring

/-- Rational form of `egyptGreedyNat`. -/
theorem egyptGreedyRat (r : ℚ) (M : ℕ) (hM : 0 < M) (h0 : 0 ≤ r) (h1 : r * M < 1) :
    ∃ S : Finset ℕ, (∀ s ∈ S, M < s) ∧ ∑ s ∈ S, (1 / (s : ℚ)) = r := by
  have hnum : ((r.num.toNat : ℕ) : ℚ) = r.num := by
    have : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 h0)
    exact_mod_cast this
  have hr : r = (r.num.toNat : ℚ) / (r.den : ℚ) := by
    rw [hnum]; exact (Rat.num_div_den r).symm
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have key : r.num.toNat * M < r.den := by
    have : ((r.num.toNat : ℕ) : ℚ) * M < r.den := by
      rw [hr, div_mul_eq_mul_div, div_lt_one hden] at h1
      exact h1
    exact_mod_cast this
  obtain ⟨S, hS1, hS2⟩ := egyptGreedyNat _ _ _ hM key
  exact ⟨S, hS1, hS2.trans hr.symm⟩

/-- The reciprocals of `A, A+1, …, 4A-1` sum to more than `1`. -/
theorem egyptBlockBig (A : ℕ) (hA : 0 < A) :
    1 < ∑ i ∈ Finset.range (A + 2 * A), (1 / ((A + i : ℕ) : ℚ)) := by
  rw [Finset.sum_range_add]
  have hA' : (0 : ℚ) < A := by exact_mod_cast hA
  have h1 : ∑ _i ∈ Finset.range A, (1 / (2 * A : ℚ)) <
      ∑ i ∈ Finset.range A, (1 / ((A + i : ℕ) : ℚ)) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.nonempty_range_iff.2 (by omega)
    · intro i hi
      rw [Finset.mem_range] at hi
      apply one_div_lt_one_div_of_lt
      · positivity
      · push_cast
        have : (i : ℚ) < A := by exact_mod_cast hi
        linarith
  have h2 : ∑ _i ∈ Finset.range (2 * A), (1 / (4 * A : ℚ)) <
      ∑ i ∈ Finset.range (2 * A), (1 / ((A + (A + i) : ℕ) : ℚ)) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.nonempty_range_iff.2 (by omega)
    · intro i hi
      rw [Finset.mem_range] at hi
      apply one_div_lt_one_div_of_lt
      · positivity
      · push_cast
        have : (i : ℚ) < 2 * A := by exact_mod_cast hi
        linarith
  have e1 : ∑ _i ∈ Finset.range A, (1 / (2 * A : ℚ)) = 1 / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have e2 : ∑ _i ∈ Finset.range (2 * A), (1 / (4 * A : ℚ)) = 1 / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  linarith

/-- A finite set of naturals `≥ N` whose reciprocals sum to `1`. -/
theorem egyptOne (N : ℕ) :
    ∃ S : Finset ℕ, (∀ s ∈ S, N ≤ s) ∧ ∑ s ∈ S, (1 / (s : ℚ)) = 1 := by
  obtain ⟨A, hAdef⟩ : ∃ A, A = N + 2 := ⟨_, rfl⟩
  have hA : 0 < A := by omega
  let f : ℕ → ℚ := fun K => ∑ i ∈ Finset.range K, (1 / ((A + i : ℕ) : ℚ))
  have hex : ∃ K, 1 < f K := ⟨A + 2 * A, egyptBlockBig A hA⟩
  obtain ⟨K1, hK1, hmin⟩ : ∃ K1, 1 < f K1 ∧ ∀ K < K1, ¬ 1 < f K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun K hK => Nat.find_min hex hK⟩
  have hK1pos : K1 ≠ 0 := by
    rintro rfl
    simp only [f, Finset.range_zero, Finset.sum_empty] at hK1
    norm_num at hK1
  obtain ⟨K, rfl⟩ : ∃ K, K1 = K + 1 := ⟨K1 - 1, by omega⟩
  have hle : f K ≤ 1 := not_lt.1 (hmin K (by omega))
  have hsucc : f (K + 1) = f K + 1 / ((A + K : ℕ) : ℚ) := Finset.sum_range_succ _ _
  have hM : 0 < A + K := by omega
  have hpos : (0 : ℚ) < ((A + K : ℕ) : ℚ) := by exact_mod_cast hM
  have hr1 : (1 - f K) * ((A + K : ℕ) : ℚ) < 1 := by
    have : 1 - f K < 1 / ((A + K : ℕ) : ℚ) := by linarith
    rwa [lt_div_iff₀ hpos] at this
  obtain ⟨S', hS'1, hS'2⟩ := egyptGreedyRat (1 - f K) (A + K) hM (by linarith) hr1
  refine ⟨Finset.Ico A (A + K) ∪ S', ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_union.1 hs with h | h
    · have := (Finset.mem_Ico.1 h).1; omega
    · have := hS'1 s h; omega
  · rw [Finset.sum_union]
    · rw [hS'2, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      show f K + (1 - f K) = 1
      ring
    · rw [Finset.disjoint_left]
      intro s h1 h2
      have := (Finset.mem_Ico.1 h1).2
      have := hS'1 s h2
      omega

theorem exists_k (N : ℕ) : ∃ (k : ℕ) (n : Fin k → ℕ),
    (∀ i, N ≤ n i) ∧ StrictMono n ∧ ∑ i, (1 / n i : ℝ) = 1 := by
  obtain ⟨S, hS1, hS2⟩ := egyptOne N
  refine ⟨S.card, S.orderEmbOfFin rfl, fun i => hS1 _ (S.orderEmbOfFin_mem rfl i),
    (S.orderEmbOfFin rfl).strictMono, ?_⟩
  have hR : ∑ s ∈ S, (1 / (s : ℝ)) = 1 := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hS2
    push_cast at this
    exact this
  refine Eq.trans ?_ hR
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ S rfl]
  rw [Finset.sum_image (fun x _ y _ h => (S.orderEmbOfFin rfl).injective h)]

end OpenProofs.Erdos295
