import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

/-!
# Shared helpers: finite graph combinatorics

Reusable, fully proved lemmas for results. Same rules as result files (see AGENTS.md "Shared
helper library"): no placeholders, everything under `OpenProofs.Lib.`, no upstream names.
-/

namespace OpenProofs.Lib

/-- Among any six vertices of a simple graph there are three that are pairwise adjacent or
pairwise non-adjacent (the pigeonhole step behind `R(3,3) = 6`). -/
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

end OpenProofs.Lib
