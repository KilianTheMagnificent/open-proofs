import FormalConjectures.ErdosProblems.«588»

/-!
# `Erdos588.erdos_588.variants.trivial_upper`

Upstream: `Erdos588.erdos_588.variants.trivial_upper` (category textbook), `FormalConjectures/ErdosProblems/588.lean` line 77.
Proof idea: double counting. Fix a finite `S` with `n` points. Send each ordered pair `(p, q)`
of distinct points of `S` whose line `affineSpan {p, q}` has exactly `k` points of `S` to that
line. The image is exactly `linesWithPointsFor k S`, and the fibre over a line `L` contains all
`k * (k - 1)` ordered pairs of distinct points of `L ∩ S` (two distinct points of a line span
it). Hence `#lines * (k * (k - 1)) ≤ #pairs ≤ n * (n - 1)`. The set in the `sSup` is therefore
bounded, so its supremum is one of its elements (or `0` if empty). The hypothesis that no
`k + 1` points are collinear is not needed.
-/

open EuclideanGeometry Filter Asymptotics
open Erdos588

namespace OpenProofs.Erdos588

theorem erdos588_trivial_upper_aux (k : ℕ) (S : Set ℝ²) (hS : S.Finite) :
    (linesWithPointsFor k S).ncard * (k * (k - 1)) ≤ S.ncard * (S.ncard - 1) := by
  classical
  set T := hS.toFinset with hT
  have hST : S.ncard = T.card := by rw [hT, Set.ncard_eq_toFinset_card S hS]
  let f : ℝ² × ℝ² → AffineSubspace ℝ ℝ² := fun x => affineSpan ℝ {x.1, x.2}
  let s := T.offDiag.filter (fun x => ((f x : Set ℝ²) ∩ S).ncard = k)
  have himg : ((s.image f : Finset _) : Set (AffineSubspace ℝ ℝ²)) = linesWithPointsFor k S := by
    ext L
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, s, Finset.mem_filter,
      Finset.mem_offDiag, hT, Set.Finite.mem_toFinset, linesWithPointsFor, Set.mem_ofPred_eq, f]
    constructor
    · rintro ⟨⟨p, q⟩, ⟨⟨hp, hq, hpq⟩, hk⟩, rfl⟩
      exact ⟨⟨p, hp, q, hq, hpq, rfl⟩, hk⟩
    · rintro ⟨⟨p, hp, q, hq, hpq, rfl⟩, hk⟩
      exact ⟨⟨p, q⟩, ⟨⟨hp, hq, hpq⟩, hk⟩, rfl⟩
  have hcard : (linesWithPointsFor k S).ncard = (s.image f).card := by
    rw [← himg, Set.ncard_coe_finset]
  have hfib : ∀ L ∈ s.image f, k * (k - 1) ≤ (s.filter (fun x => f x = L)).card := by
    intro L hL
    have hL' : L ∈ linesWithPointsFor k S := by rw [← himg]; exact hL
    obtain ⟨⟨a, ha, b, hb, hab, rfl⟩, hk⟩ := hL'
    set U := T.filter (fun p => p ∈ affineSpan ℝ ({a, b} : Set ℝ²)) with hU
    have hUc : U.card = k := by
      rw [← hk, ← Set.ncard_coe_finset]
      congr 1
      ext p
      simp [hU, hT, and_comm]
    have hsub : U.offDiag ⊆ s.filter (fun x => f x = affineSpan ℝ {a, b}) := by
      rintro ⟨p, q⟩ hpq
      simp only [Finset.mem_offDiag, hU, Finset.mem_filter] at hpq
      obtain ⟨⟨hpT, hpL⟩, ⟨hqT, hqL⟩, hne⟩ := hpq
      have heq : f (p, q) = affineSpan ℝ {a, b} :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne hpL hqL hne
      simp only [s, Finset.mem_filter, Finset.mem_offDiag]
      exact ⟨⟨⟨hpT, hqT, hne⟩, by rw [heq]; exact hk⟩, heq⟩
    calc k * (k - 1) = U.offDiag.card := by
          rw [Finset.offDiag_card, hUc, Nat.mul_sub_one]
      _ ≤ _ := Finset.card_le_card hsub
  have h1 := Finset.mul_card_image_le_card s (k * (k - 1)) hfib
  have h2 : s.card ≤ T.offDiag.card := Finset.card_filter_le _ _
  rw [Finset.offDiag_card, ← Nat.mul_sub_one] at h2
  rw [hcard, hST, mul_comm]
  exact h1.trans h2

theorem erdos_588.variants.trivial_upper (k n : ℕ) (hk : 2 ≤ k) :
    numLinesWithPointsMax k n * (k * (k - 1)) ≤ n * (n - 1) := by
  set A := {x | ∃ (S : Set ℝ²) (_ : S.ncard = n) (_ : S.Finite) (_ : NonCollinearFor (k + 1) S),
    (linesWithPointsFor k S).ncard = x} with hA
  have hmem : ∀ m ∈ A, m * (k * (k - 1)) ≤ n * (n - 1) := by
    rintro m ⟨S, hn, hfin, -, rfl⟩
    rw [← hn]
    exact erdos588_trivial_upper_aux k S hfin
  have hpos : 1 ≤ k * (k - 1) := Nat.one_le_iff_ne_zero.mpr (by
    have : 1 ≤ k - 1 := by omega
    positivity)
  show sSup A * (k * (k - 1)) ≤ n * (n - 1)
  rcases A.eq_empty_or_nonempty with he | hne
  · rw [he, csSup_empty]; simp
  · have hbdd : BddAbove A := ⟨n * (n - 1), fun m hm => by
      have := hmem m hm
      calc m = m * 1 := (mul_one m).symm
        _ ≤ m * (k * (k - 1)) := Nat.mul_le_mul_left m hpos
        _ ≤ _ := this⟩
    exact hmem _ (Nat.sSup_mem hne hbdd)

end OpenProofs.Erdos588
