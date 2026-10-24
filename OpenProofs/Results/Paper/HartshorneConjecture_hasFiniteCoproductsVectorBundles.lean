import FormalConjectures.Paper.HartshorneConjecture

/-!
# `AlgebraicGeometry.Scheme.hasFiniteCoproductsVectorBundles`

Upstream: `AlgebraicGeometry.Scheme.hasFiniteCoproductsVectorBundles` (category API), `FormalConjectures/Paper/HartshorneConjecture.lean` line 59.
Proof idea: vector bundles form a full subcategory of `S.Modules` (via `VectorBundles.toModule`),
so it suffices that the initial object and binary coproducts of `S.Modules` are vector bundles.
The initial module is free of rank 0 on the cover `{⊤}` (restriction is a left adjoint, so it
preserves initial objects, and `free PEmpty` is initial). For `M ⨿ N` with trivializing covers
`U i`, `V j`, use the cover `U i ⊓ V j`: restriction preserves binary coproducts, a free module
restricts to a free module (`overFunctorMap`, `mapFreeIso`), and `free I ⨿ free J ≅ free (I ⊕ J)`,
of rank `r + s`. Then `createsColimitOfFullyFaithfulOfIso` lifts the colimits.
-/

open CategoryTheory Limits MvPolynomial AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace OpenProofs.AlgebraicGeometry.Scheme

universe u

variable (S : Scheme.{u})

open SheafOfModules in
theorem overPreserves_hfc (U : S.Opens) :
    PreservesColimitsOfSize.{0, 0} (overFunctor S.ringCatSheaf U) :=
  (overPushforwardOverAdj (R := S.ringCatSheaf) U).leftAdjoint_preservesColimits

open SheafOfModules in
theorem freeEmptyInitial_hfc (U : S.Opens) :
    Nonempty (IsInitial (free (R := S.ringCatSheaf.over U) PEmpty)) :=
  ⟨isColimitEquivIsInitialOfIsEmpty _ _ (isColimitFreeCofan PEmpty)⟩

open SheafOfModules in
theorem vbZero_hfc {M : S.Modules} (hM : IsInitial M) :
    IsVectorBundleWithRank (J := Opens.grothendieckTopology S) M 0 := by
  let D : M.FiniteRankVectorBundleData :=
    { OpensIndex := PUnit
      opens := fun _ => ⊤
      coversTop := by
        rw [Opens.coversTop_iff]
        exact TopologicalSpace.IsOpenCover.mk (by simp)
      BasisIndex := fun _ => PEmpty
      locallyFree := fun _ =>
        have := overPreserves_hfc S ⊤
        (hM.isInitialObj (overFunctor _ ⊤)).uniqueUpToIso
        (freeEmptyInitial_hfc S ⊤).some
      finite := fun _ => inferInstance }
  exact { exists_vector_bundle_data := ⟨D, fun _ => by simp [D]⟩ }

open SheafOfModules in
noncomputable def restrictFree_hfc {U V : S.Opens} (f : V ⟶ U) {M : S.Modules} {B : Type u}
    (e : M.over U ≅ free B) : M.over V ≅ free B :=
  ((overFunctorMap _ f).app M).symm ≪≫ (overMap _ f).mapIso e ≪≫
    (mapFreeIso (overMap _ f) B (overMapUnitIso f).symm).symm

open SheafOfModules in
theorem vbCoprod_hfc {M N : S.Modules} {r s : ℕ}
    (hM : IsVectorBundleWithRank (J := Opens.grothendieckTopology S) M r)
    (hN : IsVectorBundleWithRank (J := Opens.grothendieckTopology S) N s) :
    IsVectorBundleWithRank (J := Opens.grothendieckTopology S) (M ⨿ N) (r + s) := by
  obtain ⟨D, hD⟩ := hM.exists_vector_bundle_data
  obtain ⟨E, hE⟩ := hN.exists_vector_bundle_data
  have := D.finite
  have := E.finite
  let F : (M ⨿ N).FiniteRankVectorBundleData :=
    { OpensIndex := D.OpensIndex × E.OpensIndex
      opens := fun p => D.opens p.1 ⊓ E.opens p.2
      coversTop := by
        rw [Opens.coversTop_iff]
        have hD' := (Opens.coversTop_iff _ _).1 D.coversTop
        have hE' := (Opens.coversTop_iff _ _).1 E.coversTop
        refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun x _ => ?_)
        obtain ⟨i, hi⟩ := hD'.exists_mem x
        obtain ⟨j, hj⟩ := hE'.exists_mem x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩
      BasisIndex := fun p => D.BasisIndex p.1 ⊕ E.BasisIndex p.2
      locallyFree := fun p =>
        have := overPreserves_hfc S (D.opens p.1 ⊓ E.opens p.2)
        (PreservesColimitPair.iso (overFunctor _ (D.opens p.1 ⊓ E.opens p.2)) M N).symm ≪≫
          coprod.mapIso (restrictFree_hfc S (homOfLE inf_le_left) (D.locallyFree p.1))
            (restrictFree_hfc S (homOfLE inf_le_right) (E.locallyFree p.2)) ≪≫
          freeSumIso _ _
      finite := fun p => inferInstance }
  exact { exists_vector_bundle_data := ⟨F, fun p => by simp [F, Nat.card_sum, hD, hE]⟩ }

noncomputable def toModuleFF_hfc : (VectorBundles.toModule S).FullyFaithful where
  preimage f := InducedCategory.homMk f

instance : (VectorBundles.toModule S).Full := (toModuleFF_hfc S).full
instance : (VectorBundles.toModule S).Faithful := (toModuleFF_hfc S).faithful

theorem hasFiniteCoproductsVectorBundles : HasFiniteCoproducts S.VectorBundles := by
  have : HasBinaryCoproducts S.VectorBundles := by
    refine @hasBinaryCoproducts_of_hasColimit_pair _ _ ?_
    intro A B
    let X : S.VectorBundles := ⟨A.carrier ⨿ B.carrier, A.rank + B.rank,
      vbCoprod_hfc S A.isLocallyFreeFiniteConstantRank B.isLocallyFreeFiniteConstantRank⟩
    have := createsColimitOfFullyFaithfulOfIso (K := pair A B) (F := VectorBundles.toModule S) X
      (HasColimit.isoOfNatIso (diagramIsoPair (pair A B ⋙ VectorBundles.toModule S))).symm
    exact hasColimit_of_created (pair A B) (VectorBundles.toModule S)
  have : HasInitial S.VectorBundles := by
    let X : S.VectorBundles := ⟨⊥_ S.Modules, 0, vbZero_hfc S initialIsInitial⟩
    have : ∀ K : Discrete PEmpty ⥤ S.VectorBundles,
        CreatesColimit K (VectorBundles.toModule S) := fun K =>
      createsColimitOfFullyFaithfulOfIso X (initialIsInitial.uniqueUpToIso
        (isColimitEquivIsInitialOfIsEmpty _ _ (colimit.isColimit _)))
    have : CreatesColimitsOfShape (Discrete PEmpty) (VectorBundles.toModule S) := ⟨this _⟩
    exact hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
      (VectorBundles.toModule S)
  exact hasFiniteCoproducts_of_has_binary_and_initial

end OpenProofs.AlgebraicGeometry.Scheme
