import FormalConjectures.ErdosProblems.«835»

/-!
# `Erdos835.property_iff_chromaticNumber`

Upstream: `Erdos835.property_iff_chromaticNumber` (category test), `FormalConjectures/ErdosProblems/835.lean` line 56.
Proof idea: for a `(k+1)`-set `A`, the `k`-subsets of `A` are exactly `k+1` vertices of
`J(2k, k)` and they form a clique (two distinct `k`-subsets of `A` have union `A`, hence meet in
`k-1` elements). So `χ(J(2k, k)) ≥ k+1` always, and a colouring with `k+1` colours is proper iff
it is injective, i.e. surjective, on each such clique. Hence `χ = k+1` iff `J(2k, k)` is
`(k+1)`-colourable iff `Property k`.
-/

open Finset SimpleGraph
open scoped Nat
open Erdos835

namespace OpenProofs.Erdos835

variable {n k : ℕ}

theorem p835_card_subsets (A : Finset (Fin (2 * k))) (hA : A.card = k + 1) :
    (univ.filter fun s : {s : Finset (Fin (2 * k)) // s.card = k} => s.val ⊂ A).card = k + 1 := by
  have h : (univ.filter fun s : {s : Finset (Fin (2 * k)) // s.card = k} => s.val ⊂ A).map
      (Function.Embedding.subtype _) = A.powersetCard k := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype,
      mem_powersetCard]
    constructor
    · rintro ⟨⟨s, hs⟩, hsA, rfl⟩
      exact ⟨hsA.subset, hs⟩
    · rintro ⟨hxA, hx⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      exact ssubset_of_subset_of_ne hxA fun h : x = A => by subst h; omega
  rw [← card_map, h, card_powersetCard, hA, Nat.choose_succ_self_right]

theorem p835_isClique (A : Finset (Fin (2 * k))) (hA : A.card = k + 1) :
    J(2 * k, k).IsClique
      ((univ.filter fun s : {s : Finset (Fin (2 * k)) // s.card = k} => s.val ⊂ A :
        Finset _) : Set _) := by
  intro s hs t ht hst
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  rw [johnson_adj_iff_ge]
  refine ⟨hst, ?_⟩
  have h1 := card_union_add_card_inter s.val t.val
  have h2 : (s.val ∪ t.val).card ≤ k + 1 := hA ▸ card_le_card (union_subset hs.subset ht.subset)
  rw [s.2, t.2] at h1
  omega

theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔
    Property k := by
  dsimp only [Property]
  constructor
  · intro h
    obtain ⟨C⟩ : J(2 * k, k).Colorable (k + 1) :=
      chromaticNumber_le_iff_colorable.mp (by rw [h]; push_cast; rfl)
    refine ⟨C, fun A hA => ?_⟩
    have hs := C.surjOn_of_card_le_isClique (p835_isClique A hA)
      (by rw [p835_card_subsets A hA, Fintype.card_fin])
    ext x
    simp only [mem_image, mem_univ, iff_true]
    obtain ⟨s, hs, rfl⟩ := hs (Set.mem_univ x)
    exact ⟨s, hs, rfl⟩
  · rintro ⟨c, hc⟩
    have hcol : J(2 * k, k).Colorable (k + 1) := by
      refine ⟨Coloring.mk c fun {s t} hadj => ?_⟩
      have hA : (s.val ∪ t.val).card = k + 1 := by
        have h1 := card_union_add_card_inter s.val t.val
        rw [s.2, t.2] at h1
        have h2 := hadj
        rw [johnson_adj] at h2
        omega
      have hinj : Set.InjOn c (univ.filter fun s' : {s : Finset (Fin (2 * k)) // s.card = k} =>
          s'.val ⊂ s.val ∪ t.val : Finset _) := by
        rw [← card_image_iff, hc _ hA, card_univ, Fintype.card_fin, p835_card_subsets _ hA]
      have hst : s ≠ t := hadj.ne
      have hs : s ∈ (univ.filter fun s' : {s : Finset (Fin (2 * k)) // s.card = k} =>
          s'.val ⊂ s.val ∪ t.val : Finset _) := by
        simp only [mem_filter, mem_univ, true_and]
        refine ssubset_of_subset_of_ne subset_union_left fun h => ?_
        rw [← h, s.2] at hA
        omega
      have ht : t ∈ (univ.filter fun s' : {s : Finset (Fin (2 * k)) // s.card = k} =>
          s'.val ⊂ s.val ∪ t.val : Finset _) := by
        simp only [mem_filter, mem_univ, true_and]
        refine ssubset_of_subset_of_ne subset_union_right fun h => ?_
        rw [← h, t.2] at hA
        omega
      exact fun heq => hst (hinj hs ht heq)
    apply le_antisymm (by exact_mod_cast hcol.chromaticNumber_le)
    obtain ⟨A, -, hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k))))
      (n := k + 1) (by rw [card_univ, Fintype.card_fin]; omega)
    have := (p835_isClique A hA).card_le_chromaticNumber
    rw [p835_card_subsets A hA] at this
    exact_mod_cast this

end OpenProofs.Erdos835
