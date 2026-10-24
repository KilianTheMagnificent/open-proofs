import FormalConjectures.ErdosProblems.«1069»

/-!
# `Erdos1069.erdos_1069.variants.lattice`

Upstream: `Erdos1069.erdos_1069.variants.lattice` (category textbook), `FormalConjectures/ErdosProblems/1069.lean` line 75.
Proof idea: take the grid `{(a, b) : a, b < m}` (`m ^ 2` points, the coordinate map is
injective). The `m` vertical lines `x = i` and the `m` horizontal lines `y = j` (`i, j < m`),
built as `AffineSubspace.mk'` with direction `ℝ ∙ e₁` resp. `ℝ ∙ e₀`, are lines (direction of
finrank 1) and each contains the `m` grid points `(i, j)`, `j < m` (resp. `i < m`). They are
pairwise distinct (compare which grid points they contain), so an injection
`Fin m ⊕ Fin m → richLines s m` gives `2 * m ≤ ncard` (the set is finite by `richLines_finite`).
-/

open EuclideanGeometry
open Erdos1069

namespace OpenProofs.Erdos1069

theorem lattice1069_isLine (p v : ℝ²) (hv : v ≠ 0) :
    IsLine (AffineSubspace.mk' p (Submodule.span ℝ {v})) := by
  unfold IsLine
  rw [AffineSubspace.direction_mk']
  exact finrank_span_singleton hv

theorem erdos_1069.variants.lattice (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℝ², s.card = m ^ 2 ∧ 2 * m ≤ (richLines s m).ncard := by
  classical
  let pt : ℕ × ℕ → ℝ² := fun ab => !₂[(ab.1 : ℝ), (ab.2 : ℝ)]
  have pt0 : ∀ ab, pt ab 0 = ab.1 := fun ab => by simp [pt]
  have pt1 : ∀ ab, pt ab 1 = ab.2 := fun ab => by simp [pt]
  have hpt : Function.Injective pt := by
    intro a b h
    have h0 := congrArg (fun p : ℝ² => p 0) h
    have h1 := congrArg (fun p : ℝ² => p 1) h
    simp only [pt0, pt1, Nat.cast_inj] at h0 h1
    exact Prod.ext h0 h1
  let s : Finset ℝ² := (Finset.range m ×ˢ Finset.range m).image pt
  refine ⟨s, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hpt, Finset.card_product, Finset.card_range, sq]
  let e0 : ℝ² := !₂[1, 0]
  let e1 : ℝ² := !₂[0, 1]
  have e0ne : e0 ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ² => p 0) h
    simp [e0] at this
  have e1ne : e1 ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ² => p 1) h
    simp [e1] at this
  let V : ℕ → AffineSubspace ℝ ℝ² := fun i => AffineSubspace.mk' (pt (i, 0)) (ℝ ∙ e1)
  let H : ℕ → AffineSubspace ℝ ℝ² := fun j => AffineSubspace.mk' (pt (0, j)) (ℝ ∙ e0)
  have memV : ∀ (i : ℕ) (p : ℝ²), p ∈ V i ↔ p 0 = i := by
    intro i p
    simp only [V, AffineSubspace.mem_mk', Submodule.mem_span_singleton, vsub_eq_sub]
    constructor
    · rintro ⟨a, ha⟩
      have := congrArg (fun q : ℝ² => q 0) ha
      simp [e1, pt] at this
      linarith
    · intro h
      refine ⟨p 1, ?_⟩
      ext k
      fin_cases k <;> simp [e1, pt, h]
  have memH : ∀ (j : ℕ) (p : ℝ²), p ∈ H j ↔ p 1 = j := by
    intro j p
    simp only [H, AffineSubspace.mem_mk', Submodule.mem_span_singleton, vsub_eq_sub]
    constructor
    · rintro ⟨a, ha⟩
      have := congrArg (fun q : ℝ² => q 1) ha
      simp [e0, pt] at this
      linarith
    · intro h
      refine ⟨p 0, ?_⟩
      ext k
      fin_cases k <;> simp [e0, pt, h]
  have key : ∀ (T : Set ℝ²) (f : ℕ → ℝ²), Function.Injective f → (∀ j < m, f j ∈ T) →
      T.Finite → m ≤ T.ncard := by
    intro T f hf hT hfin
    calc m = ((Finset.range m).image f).card := by
            rw [Finset.card_image_of_injective _ hf, Finset.card_range]
      _ = (((Finset.range m).image f : Finset ℝ²) : Set ℝ²).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ T.ncard := by
            refine Set.ncard_le_ncard ?_ hfin
            intro x hx
            simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
            obtain ⟨j, hj, rfl⟩ := hx
            exact hT j hj
  have sfin : ∀ L : AffineSubspace ℝ ℝ², ((s : Set ℝ²) ∩ (L : Set ℝ²)).Finite :=
    fun L => s.finite_toSet.inter_of_left _
  have memS : ∀ a b, a < m → b < m → pt (a, b) ∈ (s : Set ℝ²) := by
    intro a b ha hb
    simp only [s, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_range]
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  have Vrich : ∀ i < m, V i ∈ richLines s m := by
    intro i hi
    rw [richLines, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · exact lattice1069_isLine _ _ e1ne
    · refine key _ (fun j => pt (i, j)) (fun a b h => ?_) (fun j hj => ⟨memS i j hi hj, ?_⟩)
        (sfin _)
      · have := hpt h
        simpa using this
      · show pt (i, j) ∈ V i
        rw [memV, pt0]
  have Hrich : ∀ j < m, H j ∈ richLines s m := by
    intro j hj
    rw [richLines, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · exact lattice1069_isLine _ _ e0ne
    · refine key _ (fun i => pt (i, j)) (fun a b h => ?_) (fun i hi => ⟨memS i j hi hj, ?_⟩)
        (sfin _)
      · have := hpt h
        simpa using this
      · show pt (i, j) ∈ H j
        rw [memH, pt1]
  let L : Fin m ⊕ Fin m → AffineSubspace ℝ ℝ² := fun
    | Sum.inl i => V i
    | Sum.inr j => H j
  have hL : ∀ x, L x ∈ richLines s m := by
    rintro (i | j)
    · exact Vrich i i.isLt
    · exact Hrich j j.isLt
  have hLinj : Function.Injective L := by
    rintro (i | j) (i' | j') h
    · have h1 : pt (i, 0) ∈ V i' := by
        change pt ((i : ℕ), 0) ∈ L (Sum.inl i')
        rw [← h]; show pt ((i : ℕ), 0) ∈ V i; rw [memV, pt0]
      rw [memV, pt0, Nat.cast_inj] at h1
      exact congrArg Sum.inl (Fin.ext h1)
    · exfalso
      have h1 : pt (i, 0) ∈ H j' := by
        change pt ((i : ℕ), 0) ∈ L (Sum.inr j')
        rw [← h]; show pt ((i : ℕ), 0) ∈ V i; rw [memV, pt0]
      have h2 : pt (i, 1) ∈ H j' := by
        change pt ((i : ℕ), 1) ∈ L (Sum.inr j')
        rw [← h]; show pt ((i : ℕ), 1) ∈ V i; rw [memV, pt0]
      rw [memH, pt1] at h1 h2
      rw [← h1] at h2
      norm_num at h2
    · exfalso
      have h1 : pt (0, j) ∈ V i' := by
        change pt (0, (j : ℕ)) ∈ L (Sum.inl i')
        rw [← h]; show pt (0, (j : ℕ)) ∈ H j; rw [memH, pt1]
      have h2 : pt (1, j) ∈ V i' := by
        change pt (1, (j : ℕ)) ∈ L (Sum.inl i')
        rw [← h]; show pt (1, (j : ℕ)) ∈ H j; rw [memH, pt1]
      rw [memV, pt0] at h1 h2
      rw [← h1] at h2
      norm_num at h2
    · have h1 : pt (0, j) ∈ H j' := by
        change pt (0, (j : ℕ)) ∈ L (Sum.inr j')
        rw [← h]; show pt (0, (j : ℕ)) ∈ H j; rw [memH, pt1]
      rw [memH, pt1, Nat.cast_inj] at h1
      exact congrArg Sum.inr (Fin.ext h1)
  have hfin := richLines_finite s hm
  have := hfin.to_subtype
  have hcard : Nat.card (Fin m ⊕ Fin m) ≤ Nat.card (richLines s m) :=
    Nat.card_le_card_of_injective (fun x => ⟨L x, hL x⟩)
      (fun a b hab => hLinj (congrArg Subtype.val hab))
  rw [Nat.card_coe_set_eq, Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

end OpenProofs.Erdos1069
