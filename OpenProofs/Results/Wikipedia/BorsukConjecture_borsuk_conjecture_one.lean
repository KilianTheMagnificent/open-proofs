import FormalConjectures.Wikipedia.BorsukConjecture

/-!
# `Borsuk.borsuk_conjecture.one`

Upstream: `Borsuk.borsuk_conjecture.one` (category textbook), `FormalConjectures/Wikipedia/BorsukConjecture.lean` line 183.
Proof idea: the coordinate map `ℝ^1 → ℝ` is an isometry, so by `HasBorsukCover.isometry_image_iff`
it suffices to treat a bounded set `s ⊆ ℝ` with two points. With `a = sInf s < b = sSup s` and
midpoint `m`, the intervals `[a, m]` and `[m, b]` cover `s` and have extended diameter
`(b - a) / 2 < b - a = ediam s` (`Real.ediam_eq`, `Real.ediam_Icc`).
-/

open Metric Bornology
open scoped EuclideanGeometry
open Borsuk

namespace OpenProofs.Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

theorem borsuk_real_two_cover_aux (s : Set ℝ) (hs : IsBounded s) (hs' : s.Nontrivial) :
    HasBorsukCover 2 s := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs'
  have hbb := hs.bddBelow
  have hba := hs.bddAbove
  set a := sInf s with ha
  set b := sSup s with hb
  have hab : a < b := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact lt_of_le_of_lt (csInf_le hbb hx) (lt_of_lt_of_le h (le_csSup hba hy))
    · exact lt_of_le_of_lt (csInf_le hbb hy) (lt_of_lt_of_le h (le_csSup hba hx))
  set m := (a + b) / 2 with hm
  refine ⟨![Set.Icc a m, Set.Icc m b], ?_, ?_⟩
  · intro z hz
    have h1 : a ≤ z := csInf_le hbb hz
    have h2 : z ≤ b := le_csSup hba hz
    simp only [Set.mem_iUnion]
    rcases le_total z m with h | h
    · exact ⟨0, by simp [h1, h]⟩
    · exact ⟨1, by simp [h2, h]⟩
  · intro i
    rw [Real.ediam_eq hs]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.ediam_Icc]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [← ha, ← hb]; linarith)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Real.ediam_Icc]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [← ha, ← hb]; linarith)

theorem borsuk_euclid_one_proj_isometry_aux :
    Isometry (fun x : ℝ^1 => x 0) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.sqrt_sq dist_nonneg]

theorem borsuk_conjecture.one : BorsukConjecture 1 := by
  intro s hs hs'
  have hf := borsuk_euclid_one_proj_isometry_aux
  rw [← HasBorsukCover.isometry_image_iff hf]
  exact borsuk_real_two_cover_aux _ (hf.lipschitz.isBounded_image hs)
    (hs'.image hf.injective)

end OpenProofs.Borsuk
