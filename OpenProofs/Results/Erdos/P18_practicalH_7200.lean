import FormalConjectures.ErdosProblems.«18»

/-!
# `Erdos18.practicalH_7200`

Upstream: `Erdos18.practicalH_7200` (category test), `FormalConjectures/ErdosProblems/18.lean` line 170.
Proof idea: the minimum in `practicalH` is the least size of a set of distinct divisors of `7200`
summing to `m`. A bounded depth-first search `p7200CanSum L k m` over the descending list of the
54 divisors decides whether `m` is a sum of at most `k` distinct entries of `L` (pruning when
`m > k * head`). It is proved sound (a `true` answer yields such a set, for a duplicate-free list)
and complete (any such set forces `true`, for a descending list). Kernel `decide` then checks that
every `1 ≤ m ≤ 7200` is a sum of at most six divisors and that `6667` is not a sum of at most five.
-/

open Filter Asymptotics Real
open Erdos18

namespace OpenProofs.Erdos18

/-- Bounded depth-first search: is `m` a sum of at most `k` distinct entries of `L`?
Assumes `L` is descending for the pruning step `m ≤ k * head`. -/
noncomputable def p7200CanSum : List ℕ → ℕ → ℕ → Bool
  | [], _, m => m == 0
  | _ :: _, 0, m => m == 0
  | x :: xs, k + 1, m =>
      m == 0 || (Nat.ble m ((k + 1) * x) &&
        ((Nat.ble x m && p7200CanSum xs k (m - x)) || p7200CanSum xs (k + 1) m))

/-- The divisors of `7200`, in descending order. -/
def p7200Divs : List ℕ :=
  [7200, 3600, 2400, 1800, 1440, 1200, 900, 800, 720, 600, 480, 450, 400, 360, 300, 288, 240,
    225, 200, 180, 160, 150, 144, 120, 100, 96, 90, 80, 75, 72, 60, 50, 48, 45, 40, 36, 32, 30,
    25, 24, 20, 18, 16, 15, 12, 10, 9, 8, 6, 5, 4, 3, 2, 1]

theorem p7200CanSum_sound (L : List ℕ) (hL : L.Nodup) (k m : ℕ)
    (h : p7200CanSum L k m = true) :
    ∃ B : Finset ℕ, B ⊆ L.toFinset ∧ B.card ≤ k ∧ ∑ i ∈ B, i = m := by
  induction L generalizing k m with
  | nil =>
    simp only [p7200CanSum, beq_iff_eq] at h
    exact ⟨∅, by simp, by simp, by simp [h]⟩
  | cons x xs ih =>
    rw [List.nodup_cons] at hL
    cases k with
    | zero =>
      simp only [p7200CanSum, beq_iff_eq] at h
      exact ⟨∅, by simp, by simp, by simp [h]⟩
    | succ k =>
      simp only [p7200CanSum, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
        Nat.ble_eq] at h
      rcases h with h | ⟨-, ⟨hxm, h⟩ | h⟩
      · exact ⟨∅, by simp, by simp, by simp [h]⟩
      · obtain ⟨B, hB, hc, hs⟩ := ih hL.2 k (m - x) h
        have hxB : x ∉ B := fun hx => hL.1 (List.mem_toFinset.mp (hB hx))
        refine ⟨insert x B, ?_, ?_, ?_⟩
        · intro y hy
          rw [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · simp
          · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hB hy)))
        · rw [Finset.card_insert_of_notMem hxB]; omega
        · rw [Finset.sum_insert hxB, hs]; omega
      · obtain ⟨B, hB, hc, hs⟩ := ih hL.2 (k + 1) m h
        refine ⟨B, fun y hy => ?_, hc, hs⟩
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hB hy)))

theorem p7200CanSum_complete (L : List ℕ) (hL : L.Pairwise (· ≥ ·)) (k m : ℕ)
    (B : Finset ℕ) (hB : B ⊆ L.toFinset) (hc : B.card ≤ k) (hs : ∑ i ∈ B, i = m) :
    p7200CanSum L k m = true := by
  induction L generalizing k m B with
  | nil =>
    have : B = ∅ := by simpa using hB
    subst this
    simp only [Finset.sum_empty] at hs
    simp [p7200CanSum, ← hs]
  | cons x xs ih =>
    rw [List.pairwise_cons] at hL
    cases k with
    | zero =>
      have : B = ∅ := Finset.card_eq_zero.mp (by omega)
      subst this
      simp only [Finset.sum_empty] at hs
      simp [p7200CanSum, ← hs]
    | succ k =>
      simp only [p7200CanSum, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Nat.ble_eq]
      by_cases hm : m = 0
      · exact Or.inl hm
      right
      have hle : ∀ y ∈ B, y ≤ x := by
        intro y hy
        have := List.mem_toFinset.mp (hB hy)
        rw [List.mem_cons] at this
        rcases this with rfl | hy'
        · exact le_rfl
        · exact hL.1 y hy'
      refine ⟨?_, ?_⟩
      · calc m = ∑ i ∈ B, i := hs.symm
          _ ≤ B.card • x := Finset.sum_le_card_nsmul _ _ _ hle
          _ ≤ (k + 1) * x := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hc
      · by_cases hxB : x ∈ B
        · left
          have hsum := Finset.add_sum_erase B (fun i => i) hxB
          refine ⟨by omega, ih hL.2 k (m - x) (B.erase x) ?_ ?_ ?_⟩
          · intro y hy
            rw [Finset.mem_erase] at hy
            have := List.mem_toFinset.mp (hB hy.2)
            rw [List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hy.1
            · exact List.mem_toFinset.mpr h
          · rw [Finset.card_erase_of_mem hxB]; omega
          · omega
        · right
          refine ih hL.2 (k + 1) m B ?_ hc hs
          intro y hy
          have := List.mem_toFinset.mp (hB hy)
          rw [List.mem_cons] at this
          rcases this with rfl | h
          · exact absurd hy hxB
          · exact List.mem_toFinset.mpr h

theorem p7200Divs_nodup : p7200Divs.Nodup := by decide +kernel

theorem p7200Divs_sorted : p7200Divs.Pairwise (· ≥ ·) := by decide +kernel

theorem p7200Divs_dvd : ∀ d ∈ p7200Divs, d ∣ 7200 := by decide +kernel

/-- Checks `[a, a + n)` against `f`. -/
noncomputable def p7200Range (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, n + 1 => f a && p7200Range f (a + 1) n

theorem p7200Range_spec (f : ℕ → Bool) (a n : ℕ) (h : p7200Range f a n = true) (m : ℕ)
    (h1 : a ≤ m) (h2 : m < a + n) : f m = true := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    simp only [p7200Range, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (a + 1) h.2 (by omega) (by omega)

/-- `m` is either not a divisor of `7200` or listed, and (if positive) a sum of at most six
distinct divisors. -/
noncomputable def p7200Ok (m : ℕ) : Bool :=
  (!(7200 % m == 0) || p7200Divs.contains m) && (m == 0 || p7200CanSum p7200Divs 6 m)

theorem p7200Ok_chunk0 : p7200Range p7200Ok 0 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk1 : p7200Range p7200Ok 1000 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk2 : p7200Range p7200Ok 2000 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk3 : p7200Range p7200Ok 3000 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk4 : p7200Range p7200Ok 4000 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk5 : p7200Range p7200Ok 5000 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk6 : p7200Range p7200Ok 6000 1000 = true := by
  decide +kernel

theorem p7200Ok_chunk7 : p7200Range p7200Ok 7000 201 = true := by
  decide +kernel

theorem p7200Ok_all (m : ℕ) (hm : m < 7201) : p7200Ok m = true := by
  rcases Nat.lt_or_ge m 1000 with h0 | h0
  · exact p7200Range_spec _ _ _ p7200Ok_chunk0 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 2000 with h1 | h1
  · exact p7200Range_spec _ _ _ p7200Ok_chunk1 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 3000 with h2 | h2
  · exact p7200Range_spec _ _ _ p7200Ok_chunk2 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 4000 with h3 | h3
  · exact p7200Range_spec _ _ _ p7200Ok_chunk3 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 5000 with h4 | h4
  · exact p7200Range_spec _ _ _ p7200Ok_chunk4 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 6000 with h5 | h5
  · exact p7200Range_spec _ _ _ p7200Ok_chunk5 m (by omega) (by omega)
  rcases Nat.lt_or_ge m 7000 with h6 | h6
  · exact p7200Range_spec _ _ _ p7200Ok_chunk6 m (by omega) (by omega)
  · exact p7200Range_spec _ _ _ p7200Ok_chunk7 m (by omega) (by omega)

theorem p7200Divs_complete (d : ℕ) (hd : d ∣ 7200) : d ∈ p7200Divs := by
  have h := p7200Ok_all d (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd))
  simp only [p7200Ok, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq, List.contains_iff_mem] at h
  rcases h.1 with h' | h'
  · exact absurd (Nat.mod_eq_zero_of_dvd hd) h'
  · exact h'

theorem p7200_six (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 7200) : p7200CanSum p7200Divs 6 m = true := by
  have h := p7200Ok_all m (by omega)
  simp only [p7200Ok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.2 with h' | h'
  · omega
  · exact h'

theorem p7200_6667 : p7200CanSum p7200Divs 5 6667 = false := by decide +kernel

theorem divisors_7200_subset : Nat.divisors 7200 ⊆ p7200Divs.toFinset := by
  intro d hd
  rw [Nat.mem_divisors] at hd
  exact List.mem_toFinset.mpr
    (p7200Divs_complete d hd.1)

theorem practicalH_7200 : practicalH 7200 = 6 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨B, hB, hc, hs⟩ := p7200CanSum_sound p7200Divs p7200Divs_nodup 6 m
      (p7200_six m hm.1 hm.2)
    have hBd : B ⊆ Nat.divisors 7200 := fun d hd =>
      Nat.mem_divisors.mpr ⟨p7200Divs_dvd d (List.mem_toFinset.mp (hB hd)), by norm_num⟩
    refine le_trans (Nat.sInf_le ?_) hc
    exact ⟨B, hBd, rfl, B, subset_rfl, hs.symm⟩
  · have h6667 : (6667 : ℕ) ∈ Finset.Icc 1 7200 :=
      Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    refine le_trans ?_ (Finset.le_sup (f := fun m =>
      sInf {k | ∃ D : Finset ℕ, D ⊆ (7200 : ℕ).divisors ∧ D.card = k ∧
        m ∈ subsetSums (D : Set ℕ)}) h6667)
    apply le_csInf
    · obtain ⟨B, hB, hc, hs⟩ := p7200CanSum_sound p7200Divs p7200Divs_nodup 6 6667
        (p7200_six 6667 (by norm_num) (by norm_num))
      have hBd : B ⊆ Nat.divisors 7200 := fun d hd =>
        Nat.mem_divisors.mpr ⟨p7200Divs_dvd d (List.mem_toFinset.mp (hB hd)), by norm_num⟩
      exact ⟨B.card, B, hBd, rfl, B, subset_rfl, hs.symm⟩
    · rintro k ⟨D, hDsub, hDcard, B, hBsub, hBsum⟩
      by_contra! hk
      have hBD : B ⊆ D := Finset.coe_subset.mp hBsub
      have := p7200CanSum_complete p7200Divs p7200Divs_sorted 5 6667 B
        ((hBD.trans hDsub).trans divisors_7200_subset)
        (by have := Finset.card_le_card hBD; omega) hBsum.symm
      rw [p7200_6667] at this
      exact absurd this (by decide)

end OpenProofs.Erdos18
