import FormalConjectures.Wikipedia.RamseyNumbers
import OpenProofs.Results.Wikipedia.RamseyNumbers_three_four

/-!
# Ramsey number R(3,5) = 14

Upstream: `RamseyNumbers.ramsey_number_three_five` (formal-conjectures, Wikipedia/RamseyNumbers).
Upper bound: let `G` be a graph on `Fin 14` with no triangle and no independent set of size five,
and fix a vertex `v`. The neighbourhood of `v` is independent (no triangle), so `deg v ≤ 4`. Hence
at least nine vertices other than `v` are not adjacent to `v`; choose nine of them. The graph
induced on those nine (pulled back along an embedding `Fin 9 ↪ Fin 14`) has no triangle, and no
independent 4-set either (adding `v` would give an independent 5-set in `G`). This contradicts
`IsGraphRamsey 9 3 4`, proved in `OpenProofs.Results.Wikipedia.RamseyNumbers_three_four`. So
`IsGraphRamsey 14 3 5`. Lower bound: the circulant graph on `Fin 13` with differences `±1, ±5`
has no triangle and no independent 5-set (checked by kernel `decide`; the 5-set check runs over
increasing 5-tuples, obtained from a 5-set by `Finset.orderEmbOfFin`), so
`IsGraphRamsey 13 3 5` fails, and by monotonicity (`IsGraphRamsey.succ`) so does every smaller
size. The value follows from `classicalRamsey_eq_sInf`.
-/

open RamseyNumbers

namespace OpenProofs.RamseyNumbers

namespace R35

/-- Every graph on fourteen vertices has a triangle or an independent set of size five. -/
theorem fourteen_forces_triangle_or_indep_five : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hGc⟩
  have tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False :=
    fun a b c h1 h2 h3 => hG {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ⟨h1, h2, h3⟩)
  let v : Fin 14 := 0
  have deg_le : G.degree v ≤ 4 := by
    by_contra hlt
    obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := 5)
      (by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
    apply hGc u
    refine (SimpleGraph.isNClique_iff _).2 ⟨?_, hcard⟩
    intro x hx y hy hxy
    rw [SimpleGraph.compl_adj]
    refine ⟨hxy, fun hxy' => tri v x y ?_ ?_ hxy'⟩
    · exact (SimpleGraph.mem_neighborFinset _ _ _).1 (hu hx)
    · exact (SimpleGraph.mem_neighborFinset _ _ _).1 (hu hy)
  have hM : 9 ≤ ((Finset.univ.filter fun w => ¬G.Adj v w).erase v).card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 14))) (G.Adj v)
    have h2 : (Finset.univ.filter (G.Adj v)).card = G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    have h3 : v ∈ Finset.univ.filter fun w => ¬G.Adj v w := by simp
    rw [Finset.card_erase_of_mem h3]
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨t, htM, htcard⟩ := Finset.exists_subset_card_eq hM
  let e : Fin 9 ↪ Fin 14 := (t.orderEmbOfFin htcard).toEmbedding
  have he : ∀ i, e i ≠ v ∧ ¬G.Adj v (e i) := by
    intro i
    have := htM (Finset.orderEmbOfFin_mem t htcard i)
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  let H : SimpleGraph (Fin 9) := G.comap e
  apply R34.nine_forces_triangle_or_indep_four H
  refine ⟨hG.comap (SimpleGraph.Embedding.comap e G).isContained, ?_⟩
  intro s hs
  apply hGc (insert v (s.map e))
  refine SimpleGraph.IsNClique.insert ((SimpleGraph.isNClique_iff _).2 ⟨?_, ?_⟩) ?_
  · intro x hx y hy hxy
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    have hij : i ≠ j := fun h => hxy (h ▸ rfl)
    have := hs.isClique hi hj hij
    rw [SimpleGraph.compl_adj] at this ⊢
    exact ⟨hxy, this.2⟩
  · rw [Finset.card_map, hs.card_eq]
  · intro b hb
    simp only [Finset.mem_map] at hb
    obtain ⟨i, -, rfl⟩ := hb
    rw [SimpleGraph.compl_adj]
    exact ⟨(he i).1.symm, (he i).2⟩

/-- The circulant graph on `Fin 13` with differences `±1` and `±5`. -/
def circ13Graph : SimpleGraph (Fin 13) where
  Adj i j := j - i = 1 ∨ j - i = 5 ∨ j - i = 8 ∨ j - i = 12
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance circ13Graph_decidableAdj : DecidableRel circ13Graph.Adj :=
  fun i j => inferInstanceAs (Decidable (j - i = 1 ∨ j - i = 5 ∨ j - i = 8 ∨ j - i = 12))

theorem circ13Graph_cliqueFree : circ13Graph.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  have key : ∀ a b : Fin 13, circ13Graph.Adj a b → ∀ c : Fin 13,
      circ13Graph.Adj a c → ¬circ13Graph.Adj b c := by
    decide
  exact key a b hab c hac hbc

set_option synthInstance.maxSize 2048 in
theorem circ13Graph_compl_cliqueFree : (circ13Graph)ᶜ.CliqueFree 5 := by
  intro t ht
  have key : ∀ a b : Fin 13, a < b → ¬circ13Graph.Adj a b →
      ∀ c : Fin 13, b < c → ¬circ13Graph.Adj a c → ¬circ13Graph.Adj b c →
      ∀ d : Fin 13, c < d → ¬circ13Graph.Adj a d → ¬circ13Graph.Adj b d →
        ¬circ13Graph.Adj c d →
      ∀ e : Fin 13, d < e → ¬circ13Graph.Adj a e → ¬circ13Graph.Adj b e →
        ¬circ13Graph.Adj c e → circ13Graph.Adj d e := by
    decide
  let f := t.orderEmbOfFin ht.card_eq
  have hn : ∀ i j : Fin 5, i < j → ¬circ13Graph.Adj (f i) (f j) := fun i j hij =>
    (ht.isClique (Finset.orderEmbOfFin_mem t ht.card_eq i)
      (Finset.orderEmbOfFin_mem t ht.card_eq j) (f.strictMono hij).ne).2
  exact hn 3 4 (by decide) (key (f 0) (f 1) (f.strictMono (by decide)) (hn 0 1 (by decide))
    (f 2) (f.strictMono (by decide)) (hn 0 2 (by decide)) (hn 1 2 (by decide))
    (f 3) (f.strictMono (by decide)) (hn 0 3 (by decide)) (hn 1 3 (by decide))
    (hn 2 3 (by decide))
    (f 4) (f.strictMono (by decide)) (hn 0 4 (by decide)) (hn 1 4 (by decide))
    (hn 2 4 (by decide)))

/-- No graph-Ramsey property for `(3, 5)` on at most thirteen vertices. -/
theorem not_isGraphRamsey_le_thirteen {n : ℕ} (hn : n ≤ 13) : ¬IsGraphRamsey n 3 5 := by
  intro h
  have h13 : IsGraphRamsey 13 3 5 :=
    Nat.le_induction h (fun k _ ih => IsGraphRamsey.succ k 3 5 ih) 13 hn
  exact h13 circ13Graph ⟨circ13Graph_cliqueFree, circ13Graph_compl_cliqueFree⟩

end R35

open R35 in
theorem ramsey_number_three_five : SimpleGraph.classicalRamsey 3 5 = 14 := by
  rw [classicalRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le fourteen_forces_triangle_or_indep_five)
  refine le_csInf ⟨14, fourteen_forces_triangle_or_indep_five⟩ fun n hn => ?_
  by_contra hlt
  exact not_isGraphRamsey_le_thirteen (by omega) hn

end OpenProofs.RamseyNumbers
