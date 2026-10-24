import FormalConjectures.ErdosProblems.«18»

/-!
# `Erdos18.practicalH_fiftysix`

Upstream: `Erdos18.practicalH_fiftysix` (category test), `FormalConjectures/ErdosProblems/18.lean` line 163.
Proof idea: the minimum in `practicalH` is the least size of a set of distinct divisors of `56`
summing to `m`. A bounded depth-first search `p56CanSum L k m` over the descending list of the
eight divisors decides whether `m` is a sum of at most `k` distinct entries of `L` (pruning when
`m > k * head`). It is proved sound (a `true` answer yields such a set, for a duplicate-free list)
and complete (any such set forces `true`, for a descending list). Kernel `decide` then checks that
every `1 ≤ m ≤ 56` is a sum of at most five divisors and that `55 = 28 + 14 + 8 + 4 + 1` is not a
sum of at most four.
-/

open Filter Asymptotics Real
open Erdos18

namespace OpenProofs.Erdos18

/-- Bounded depth-first search: is `m` a sum of at most `k` distinct entries of `L`?
Assumes `L` is descending for the pruning step `m ≤ k * head`. -/
noncomputable def p56CanSum : List ℕ → ℕ → ℕ → Bool
  | [], _, m => m == 0
  | _ :: _, 0, m => m == 0
  | x :: xs, k + 1, m =>
      m == 0 || (Nat.ble m ((k + 1) * x) &&
        ((Nat.ble x m && p56CanSum xs k (m - x)) || p56CanSum xs (k + 1) m))

/-- The divisors of `56`, in descending order. -/
def p56Divs : List ℕ := [56, 28, 14, 8, 7, 4, 2, 1]

theorem p56CanSum_sound (L : List ℕ) (hL : L.Nodup) (k m : ℕ)
    (h : p56CanSum L k m = true) :
    ∃ B : Finset ℕ, B ⊆ L.toFinset ∧ B.card ≤ k ∧ ∑ i ∈ B, i = m := by
  induction L generalizing k m with
  | nil =>
    simp only [p56CanSum, beq_iff_eq] at h
    exact ⟨∅, by simp, by simp, by simp [h]⟩
  | cons x xs ih =>
    rw [List.nodup_cons] at hL
    cases k with
    | zero =>
      simp only [p56CanSum, beq_iff_eq] at h
      exact ⟨∅, by simp, by simp, by simp [h]⟩
    | succ k =>
      simp only [p56CanSum, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
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

theorem p56CanSum_complete (L : List ℕ) (hL : L.Pairwise (· ≥ ·)) (k m : ℕ)
    (B : Finset ℕ) (hB : B ⊆ L.toFinset) (hc : B.card ≤ k) (hs : ∑ i ∈ B, i = m) :
    p56CanSum L k m = true := by
  induction L generalizing k m B with
  | nil =>
    have : B = ∅ := by simpa using hB
    subst this
    simp only [Finset.sum_empty] at hs
    simp [p56CanSum, ← hs]
  | cons x xs ih =>
    rw [List.pairwise_cons] at hL
    cases k with
    | zero =>
      have : B = ∅ := Finset.card_eq_zero.mp (by omega)
      subst this
      simp only [Finset.sum_empty] at hs
      simp [p56CanSum, ← hs]
    | succ k =>
      simp only [p56CanSum, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Nat.ble_eq]
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

theorem p56Divs_nodup : p56Divs.Nodup := by decide +kernel

theorem p56Divs_sorted : p56Divs.Pairwise (· ≥ ·) := by decide +kernel

theorem p56Divs_dvd : ∀ d ∈ p56Divs, d ∣ 56 := by decide +kernel

theorem p56_divisors_eq : Nat.divisors 56 = p56Divs.toFinset := by decide +kernel

theorem p56_five : ∀ m < 57, 1 ≤ m → p56CanSum p56Divs 5 m = true := by decide +kernel

theorem p56_55 : p56CanSum p56Divs 4 55 = false := by decide +kernel

theorem practicalH_fiftysix : practicalH 56 = 5 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨B, hB, hc, hs⟩ := p56CanSum_sound p56Divs p56Divs_nodup 5 m
      (p56_five m (by omega) hm.1)
    have hBd : B ⊆ Nat.divisors 56 := p56_divisors_eq ▸ hB
    refine le_trans (Nat.sInf_le ?_) hc
    exact ⟨B, hBd, rfl, B, subset_rfl, hs.symm⟩
  · have h55 : (55 : ℕ) ∈ Finset.Icc 1 56 :=
      Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    refine le_trans ?_ (Finset.le_sup (f := fun m =>
      sInf {k | ∃ D : Finset ℕ, D ⊆ (56 : ℕ).divisors ∧ D.card = k ∧
        m ∈ subsetSums (D : Set ℕ)}) h55)
    apply le_csInf
    · obtain ⟨B, hB, hc, hs⟩ := p56CanSum_sound p56Divs p56Divs_nodup 5 55
        (p56_five 55 (by norm_num) (by norm_num))
      have hBd : B ⊆ Nat.divisors 56 := p56_divisors_eq ▸ hB
      exact ⟨B.card, B, hBd, rfl, B, subset_rfl, hs.symm⟩
    · rintro k ⟨D, hDsub, hDcard, B, hBsub, hBsum⟩
      by_contra! hk
      have hBD : B ⊆ D := Finset.coe_subset.mp hBsub
      have := p56CanSum_complete p56Divs p56Divs_sorted 4 55 B
        (p56_divisors_eq ▸ hBD.trans hDsub)
        (by have := Finset.card_le_card hBD; omega) hBsum.symm
      rw [p56_55] at this
      exact absurd this (by decide)

end OpenProofs.Erdos18
