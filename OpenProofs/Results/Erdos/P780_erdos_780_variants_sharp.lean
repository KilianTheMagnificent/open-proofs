import FormalConjectures.ErdosProblems.«780»

/-!
# `Erdos780.erdos_780.variants.sharp`

Upstream: `Erdos780.erdos_780.variants.sharp` (category textbook), `FormalConjectures/ErdosProblems/780.lean` line 60.
Proof idea: with `n = kr - 1 + (t - 1)(k - 1)`, colour an `r`-set by the block of its maximum
element, where block `0` is `[0, kr - 1)` and block `i ≥ 1` is
`[kr - 1 + (i - 1)(k - 1), kr - 1 + i(k - 1))`. Colour `0` edges lie in a set of size `kr - 1`,
so `k` disjoint ones (total size `kr`) cannot fit. Colour `i ≥ 1` edges have their maxima in a
block of size `k - 1`, and disjoint edges have distinct maxima, so there are at most `k - 1`.
-/

open Erdos780

namespace OpenProofs.Erdos780

theorem erdos_780.variants.sharp (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1 := by
  generalize hn : k * r - 1 + (t - 1) * (k - 1) = n
  have hkr : 1 ≤ k * r := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hne : ∀ e : {e : Finset (Fin n) // e.card = r}, e.1.Nonempty := fun e => by
    rw [← Finset.card_pos, e.2]; omega
  let col : ℕ → ℕ := fun v => if v < k * r - 1 then 0 else (v - (k * r - 1)) / (k - 1) + 1
  refine ⟨fun e => ⟨min (t - 1) (col (e.1.max' (hne e)).val), by omega⟩, ?_⟩
  rintro ⟨i, e, hc, hd⟩
  set m : Fin k → Fin n := fun j => (e j).1.max' (hne (e j)) with hm
  have hmem : ∀ j, m j ∈ (e j).1 := fun j => Finset.max'_mem _ _
  have hcol : ∀ j, min (t - 1) (col (m j).val) = i.val := fun j => by
    have := congrArg Fin.val (hc j)
    simpa using this
  have hinj : ∀ j₁ j₂, m j₁ = m j₂ → j₁ = j₂ := by
    intro j₁ j₂ h
    by_contra hne'
    exact Finset.disjoint_left.mp (hd hne') (hmem j₁) (h ▸ hmem j₂)
  by_cases hi : i.val = 0
  · have hsmall : ∀ j, (m j).val < k * r - 1 := by
      intro j
      have h1 := hcol j
      have h2 := (m j).isLt
      simp only [col] at h1
      split_ifs at h1 with h3
      · exact h3
      · have ht1 : t - 1 = 0 := by
          have h4 := h1.trans hi
          rw [min_def] at h4
          split_ifs at h4 with h5
          exact h4
        rw [ht1, zero_mul] at hn
        omega
    have hsub : ∀ j, ∀ v ∈ (e j).1, v.val < k * r - 1 := fun j v hv =>
      lt_of_le_of_lt (Finset.le_max' _ _ hv) (hsmall j)
    have hcard : (Finset.univ.biUnion fun j => (e j).1).card = k * r := by
      rw [Finset.card_biUnion]
      · simp [(e _).2]
      · intro x _ y _ hxy; exact hd hxy
    have hle : (Finset.univ.biUnion fun j => (e j).1).card ≤ (Finset.range (k * r - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun v => v.val)
      · intro v hv
        simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
          Set.mem_iUnion, Finset.mem_coe] at hv
        obtain ⟨j, hj⟩ := hv
        simpa using hsub j v hj
      · intro a _ b _ hab; exact Fin.ext hab
    simp at hle
    omega
  · have hbig : ∀ j, k * r - 1 ≤ (m j).val ∧ 0 < k - 1 ∧
        ((m j).val - (k * r - 1)) / (k - 1) = i.val - 1 := by
      intro j
      have h1 := hcol j
      have h2 := (m j).isLt
      simp only [col] at h1
      split_ifs at h1 with h3
      · omega
      · have hk1 : 0 < k - 1 := by
          apply Nat.pos_of_ne_zero
          intro h
          rw [h, mul_zero] at hn
          omega
        have hq : ((m j).val - (k * r - 1)) / (k - 1) < t - 1 := by
          rw [Nat.div_lt_iff_lt_mul hk1]; omega
        rw [min_def] at h1
        split_ifs at h1 <;> refine ⟨by omega, hk1, by omega⟩
    obtain ⟨-, hk1, -⟩ := hbig ⟨0, by omega⟩
    have hle : (Finset.univ : Finset (Fin k)).card ≤ (Finset.range (k - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun j => ((m j).val - (k * r - 1)) % (k - 1))
      · intro j _
        simpa using Nat.mod_lt ((m j).val - (k * r - 1)) hk1
      · intro a _ b _ hab
        apply hinj
        apply Fin.ext
        have ha := hbig a
        have hb := hbig b
        have e1 := Nat.div_add_mod ((m a).val - (k * r - 1)) (k - 1)
        have e2 := Nat.div_add_mod ((m b).val - (k * r - 1)) (k - 1)
        simp only at hab
        rw [ha.2.2] at e1
        rw [hb.2.2] at e2
        rw [hab] at e1
        omega
    simp at hle
    omega

end OpenProofs.Erdos780
