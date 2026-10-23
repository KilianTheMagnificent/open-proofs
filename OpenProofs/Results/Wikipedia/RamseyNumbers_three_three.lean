import FormalConjectures.Wikipedia.RamseyNumbers

/-!
# Ramsey number R(3,3) = 6

Upstream: `RamseyNumbers.ramsey_number_three_three` (formal-conjectures, Wikipedia/RamseyNumbers).
Upper bound: among any six vertices pick one, `v`; of the remaining five, at least three are all
adjacent to `v` or all non-adjacent to `v`. If two of those three agree with `v`'s colour we get a
monochromatic triangle through `v`; otherwise the three form a triangle of the other colour. So every
graph on `Fin 6` has a triangle or an independent triple, i.e. `IsGraphRamsey 6 3 3`. Lower bound:
the 5-cycle on `Fin 5` has no triangle and no independent triple (checked by kernel `decide`), so
`IsGraphRamsey 5 3 3` fails, and by monotonicity (`IsGraphRamsey.succ`) so does every smaller
size. The value then follows from `classicalRamsey_eq_sInf`.
-/

open RamseyNumbers

namespace OpenProofs.RamseyNumbers

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

/-- Every graph on six vertices has a triangle or an independent set of size three. -/
theorem six_forces_mono_triangle : IsGraphRamsey 6 3 3 := by
  rintro G ⟨hG, hGc⟩
  obtain ⟨a, -, b, -, c, -, hab, hac, hbc, h | h⟩ :=
    mono_triple_of_six_le_card G Finset.univ (by simp)
  · exact hG {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 h)
  · refine hGc {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ?_)
    simp only [SimpleGraph.compl_adj]
    exact ⟨⟨hab, h.1⟩, ⟨hac, h.2.1⟩, ⟨hbc, h.2.2⟩⟩

/-- The 5-cycle on `Fin 5`: `i` is adjacent to `i ± 1 (mod 5)`. -/
def cycle5Graph : SimpleGraph (Fin 5) where
  Adj i j := j = i + 1 ∨ i = j + 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance cycle5Graph_decidableAdj : DecidableRel cycle5Graph.Adj :=
  fun i j => inferInstanceAs (Decidable (j = i + 1 ∨ i = j + 1))

theorem cycle5Graph_cliqueFree : cycle5Graph.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  have key : ∀ a b c : Fin 5,
      ¬(cycle5Graph.Adj a b ∧ cycle5Graph.Adj a c ∧ cycle5Graph.Adj b c) := by
    decide
  exact key a b c ⟨hab, hac, hbc⟩

theorem cycle5Graph_compl_cliqueFree : (cycle5Graph)ᶜ.CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.1 ht
  have key : ∀ a b c : Fin 5,
      ¬((cycle5Graph)ᶜ.Adj a b ∧ (cycle5Graph)ᶜ.Adj a c ∧ (cycle5Graph)ᶜ.Adj b c) := by
    decide
  exact key a b c ⟨hab, hac, hbc⟩

/-- No graph-Ramsey property for `(3, 3)` on at most five vertices. -/
theorem not_isGraphRamsey_le_five {n : ℕ} (hn : n ≤ 5) : ¬IsGraphRamsey n 3 3 := by
  intro h
  have h5 : IsGraphRamsey 5 3 3 :=
    Nat.le_induction h (fun k _ ih => IsGraphRamsey.succ k 3 3 ih) 5 hn
  exact h5 cycle5Graph ⟨cycle5Graph_cliqueFree, cycle5Graph_compl_cliqueFree⟩

theorem ramsey_number_three_three : SimpleGraph.classicalRamsey 3 3 = 6 := by
  rw [classicalRamsey_eq_sInf]
  apply le_antisymm (Nat.sInf_le six_forces_mono_triangle)
  refine le_csInf ⟨6, six_forces_mono_triangle⟩ fun n hn => ?_
  by_contra hlt
  exact not_isGraphRamsey_le_five (by omega) hn

end OpenProofs.RamseyNumbers
