import FormalConjectures.Wikipedia.RamseyNumbers

/-!
# Ramsey number R(3,4) = 9

Upstream: `RamseyNumbers.ramsey_number_three_four` (formal-conjectures, Wikipedia/RamseyNumbers).
Upper bound: let `G` be a graph on `Fin 9` with no triangle and no independent set of size four.
The neighbourhood of any vertex `v` is independent (no triangle), so `deg v ≤ 3`. The vertices
other than `v` and its neighbours contain no triangle and no independent triple (that triple
plus `v` would be an independent 4-set); by the six-vertex argument behind R(3,3) = 6 there are at
most five of them, so `deg v ≥ 3`. Hence every degree is 3, and the degree sum `9 * 3 = 27` is odd,
contradicting the handshake lemma. So `IsGraphRamsey 9 3 4`. Lower bound: the Wagner graph (the
circulant graph on `Fin 8` with differences `±1, 4`) has no triangle and no independent 4-set
(checked by kernel `decide`), so `IsGraphRamsey 8 3 4` fails, and by monotonicity
(`IsGraphRamsey.succ`) so does every smaller size. The value follows from
`classicalRamsey_eq_sInf`.
-/

open RamseyNumbers

namespace OpenProofs.RamseyNumbers

namespace R34

/-- Among any six vertices of a simple graph there are three that are pairwise adjacent or
pairwise non-adjacent. -/
theorem mono_triple_of_six_le_card {V : Type*} (G : SimpleGraph V) (s : Finset V)
    (hs : 6 ≤ s.card) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ((G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) ∨ (¬G.Adj a b ∧ ¬G.Adj a c ∧ ¬G.Adj b c)) := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  have ht : 5 ≤ (s.erase v).card := by rw [Finset.card_erase_of_mem hv]; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := s.erase v) (G.Adj v)
  by_cases hbig : 3 ≤ ((s.erase v).filter (G.Adj v)).card
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card.1 (by omega : 2 < ((s.erase v).filter (G.Adj v)).card)
    simp only [Finset.mem_filter, Finset.mem_erase] at ha hb hc
    by_cases h1 : G.Adj a b
    · exact ⟨v, hv, a, ha.1.2, b, hb.1.2, Ne.symm ha.1.1, Ne.symm hb.1.1, hab,
        Or.inl ⟨ha.2, hb.2, h1⟩⟩
    by_cases h2 : G.Adj a c
    · exact ⟨v, hv, a, ha.1.2, c, hc.1.2, Ne.symm ha.1.1, Ne.symm hc.1.1, hac,
        Or.inl ⟨ha.2, hc.2, h2⟩⟩
    by_cases h3 : G.Adj b c
    · exact ⟨v, hv, b, hb.1.2, c, hc.1.2, Ne.symm hb.1.1, Ne.symm hc.1.1, hbc,
        Or.inl ⟨hb.2, hc.2, h3⟩⟩
    exact ⟨a, ha.1.2, b, hb.1.2, c, hc.1.2, hab, hac, hbc, Or.inr ⟨h1, h2, h3⟩⟩
  · obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card.1 (by omega : 2 < ((s.erase v).filter fun w => ¬G.Adj v w).card)
    simp only [Finset.mem_filter, Finset.mem_erase] at ha hb hc
    by_cases h1 : G.Adj a b
    · by_cases h2 : G.Adj a c
      · by_cases h3 : G.Adj b c
        · exact ⟨a, ha.1.2, b, hb.1.2, c, hc.1.2, hab, hac, hbc, Or.inl ⟨h1, h2, h3⟩⟩
        · exact ⟨v, hv, b, hb.1.2, c, hc.1.2, Ne.symm hb.1.1, Ne.symm hc.1.1, hbc,
            Or.inr ⟨hb.2, hc.2, h3⟩⟩
      · exact ⟨v, hv, a, ha.1.2, c, hc.1.2, Ne.symm ha.1.1, Ne.symm hc.1.1, hac,
          Or.inr ⟨ha.2, hc.2, h2⟩⟩
    · exact ⟨v, hv, a, ha.1.2, b, hb.1.2, Ne.symm ha.1.1, Ne.symm hb.1.1, hab,
        Or.inr ⟨ha.2, hb.2, h1⟩⟩

/-- Four distinct pairwise non-adjacent vertices give a 4-clique in the complement. -/
theorem not_compl_cliqueFree_four {V : Type*} [DecidableEq V] (G : SimpleGraph V) {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : ¬G.Adj a b) (h2 : ¬G.Adj a c) (h3 : ¬G.Adj a d) (h4 : ¬G.Adj b c)
    (h5 : ¬G.Adj b d) (h6 : ¬G.Adj c d) :
    ¬(Gᶜ).CliqueFree 4 := by
  intro h
  apply h (insert a {b, c, d})
  refine SimpleGraph.IsNClique.insert (SimpleGraph.is3Clique_triple_iff.2 ?_) ?_
  · simp only [SimpleGraph.compl_adj]
    exact ⟨⟨hbc, h4⟩, ⟨hbd, h5⟩, ⟨hcd, h6⟩⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [SimpleGraph.compl_adj]
    rcases hx with rfl | rfl | rfl
    · exact ⟨hab, h1⟩
    · exact ⟨hac, h2⟩
    · exact ⟨had, h3⟩

/-- Every graph on nine vertices has a triangle or an independent set of size four. -/
theorem nine_forces_triangle_or_indep_four : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hGc⟩
  have tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False :=
    fun a b c h1 h2 h3 => hG {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ⟨h1, h2, h3⟩)
  have deg_le : ∀ v, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (s := G.neighborFinset v) (n := 4)
      (by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
    apply hGc u
    refine (SimpleGraph.isNClique_iff _).2 ⟨?_, hcard⟩
    intro x hx y hy hxy
    rw [SimpleGraph.compl_adj]
    refine ⟨hxy, fun hxy' => tri v x y ?_ ?_ hxy'⟩
    · exact (SimpleGraph.mem_neighborFinset _ _ _).1 (hu hx)
    · exact (SimpleGraph.mem_neighborFinset _ _ _).1 (hu hy)
  have deg_ge : ∀ v, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    have hM : 6 ≤ ((Finset.univ.filter fun w => ¬G.Adj v w).erase v).card := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 9))) (G.Adj v)
      have h2 : (Finset.univ.filter (G.Adj v)).card = G.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      have h3 : v ∈ Finset.univ.filter fun w => ¬G.Adj v w := by simp
      rw [Finset.card_erase_of_mem h3]
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, h | h⟩ := mono_triple_of_six_le_card G _ hM
    · exact tri a b c h.1 h.2.1 h.2.2
    · simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
      exact not_compl_cliqueFree_four G (Ne.symm ha.1) (Ne.symm hb.1) (Ne.symm hc.1) hab hac hbc
        ha.2 hb.2 hc.2 h.1 h.2.1 h.2.2 hGc
  have hsum := G.sum_degrees_eq_twice_card_edges
  have h27 : ∑ v, G.degree v = 27 := by
    rw [Finset.sum_congr rfl fun v _ => le_antisymm (deg_le v) (deg_ge v)]
    simp
  omega

/-- The Wagner graph: the circulant graph on `Fin 8` with differences `±1` and `4`. -/
def wagnerGraph : SimpleGraph (Fin 8) where
  Adj i j := j - i = 1 ∨ j - i = 4 ∨ j - i = 7
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance wagnerGraph_decidableAdj : DecidableRel wagnerGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (j - i = 1 ∨ j - i = 4 ∨ j - i = 7))

theorem wagnerGraph_cliqueFree : wagnerGraph.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  have key : ∀ a b : Fin 8, wagnerGraph.Adj a b → ∀ c : Fin 8,
      wagnerGraph.Adj a c → ¬wagnerGraph.Adj b c := by
    decide
  exact key a b hab c hac hbc

theorem wagnerGraph_compl_cliqueFree : (wagnerGraph)ᶜ.CliqueFree 4 := by
  intro t ht
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 ht.card_eq
  have key : ∀ a b : Fin 8, (wagnerGraph)ᶜ.Adj a b → ∀ c : Fin 8,
      (wagnerGraph)ᶜ.Adj a c → (wagnerGraph)ᶜ.Adj b c → ∀ d : Fin 8,
      (wagnerGraph)ᶜ.Adj a d → (wagnerGraph)ᶜ.Adj b d → ¬(wagnerGraph)ᶜ.Adj c d := by
    decide
  have hcl := ht.isClique
  exact key a b (hcl (by simp) (by simp) hab) c (hcl (by simp) (by simp) hac)
    (hcl (by simp) (by simp) hbc) d (hcl (by simp) (by simp) had)
    (hcl (by simp) (by simp) hbd) (hcl (by simp) (by simp) hcd)

/-- No graph-Ramsey property for `(3, 4)` on at most eight vertices. -/
theorem not_isGraphRamsey_le_eight {n : ℕ} (hn : n ≤ 8) : ¬IsGraphRamsey n 3 4 := by
  intro h
  have h8 : IsGraphRamsey 8 3 4 :=
    Nat.le_induction h (fun k _ ih => IsGraphRamsey.succ k 3 4 ih) 8 hn
  exact h8 wagnerGraph ⟨wagnerGraph_cliqueFree, wagnerGraph_compl_cliqueFree⟩

end R34

open R34 in
theorem ramsey_number_three_four : SimpleGraph.classicalRamsey 3 4 = 9 := by
  rw [classicalRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le nine_forces_triangle_or_indep_four)
  refine le_csInf ⟨9, nine_forces_triangle_or_indep_four⟩ fun n hn => ?_
  by_contra hlt
  exact not_isGraphRamsey_le_eight (by omega) hn

end OpenProofs.RamseyNumbers
