import FormalConjectures.WrittenOnTheWallII.Test

/-!
# Written on the Wall II tests: `petersen_girth`

Upstream: `WrittenOnTheWallII.Test.petersen_girth` (category test): `PetersenGraph.girth = 5`.

The outer 5-cycle `0-1-2-3-4-0` is a cycle of length `5`, so the girth is at most `5`. A cycle of
length `3` gives a closed adjacency chain `a ~ b ~ c ~ a`; a cycle of length `4` gives
`a ~ b ~ c ~ d ~ a` with `a ≠ c` and `b ≠ d` (from the nodup support). Kernel `decide` (through
an explicit edge list for the adjacency) shows the Petersen graph has neither, and every cycle
has length at least `3`, so every cycle has length at least `5`. Then `egirth = 5` and
`girth = 5`.

The generic walk lemmas here are reused by the `C6_girth` result.
-/

open WrittenOnTheWallII.Test SimpleGraph

namespace OpenProofs.WrittenOnTheWallII.Test

variable {V : Type*} {G : SimpleGraph V}

/-- A closed walk of length three gives a closed adjacency chain `a ~ b ~ c ~ a`. -/
theorem cycle_len_three_wow {a : V} (w : G.Walk a a) (hl : w.length = 3) :
    ∃ b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by
  rcases w with _ | ⟨h1, w⟩; · simp at hl
  rcases w with _ | ⟨h2, w⟩; · simp at hl
  rcases w with _ | ⟨h3, w⟩; · simp at hl
  rcases w with _ | ⟨h4, w⟩
  · exact ⟨_, _, h1, h2, h3⟩
  · simp at hl

/-- A cycle of length four gives `a ~ b ~ c ~ d ~ a` with `a ≠ c` and `b ≠ d`. -/
theorem cycle_len_four_wow {a : V} (w : G.Walk a a) (hw : w.IsCycle) (hl : w.length = 4) :
    ∃ b c d, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ a ≠ c ∧ b ≠ d := by
  have hn := hw.support_nodup
  rcases w with _ | ⟨h1, w⟩; · simp at hl
  rcases w with _ | ⟨h2, w⟩; · simp at hl
  rcases w with _ | ⟨h3, w⟩; · simp at hl
  rcases w with _ | ⟨h4, w⟩; · simp at hl
  rcases w with _ | ⟨h5, w⟩
  · simp at hn
    exact ⟨_, _, _, h1, h2, h3, h4, fun h => hn.2.1.2 h.symm, hn.1.2.1⟩
  · simp at hl

/-- A closed walk of length five gives a closed adjacency chain of five steps. -/
theorem cycle_len_five_wow {a : V} (w : G.Walk a a) (hl : w.length = 5) :
    ∃ b c d e, G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a := by
  rcases w with _ | ⟨h1, w⟩; · simp at hl
  rcases w with _ | ⟨h2, w⟩; · simp at hl
  rcases w with _ | ⟨h3, w⟩; · simp at hl
  rcases w with _ | ⟨h4, w⟩; · simp at hl
  rcases w with _ | ⟨h5, w⟩; · simp at hl
  rcases w with _ | ⟨h6, w⟩
  · exact ⟨_, _, _, _, h1, h2, h3, h4, h5⟩
  · simp at hl

/-- A graph with a cycle of length `n` and no shorter cycle has girth `n`. -/
theorem girth_eq_of_cycle_wow {a : V} (w : G.Walk a a) (hw : w.IsCycle) {n : ℕ}
    (hl : w.length = n) (hmin : ∀ (b : V) (w' : G.Walk b b), w'.IsCycle → n ≤ w'.length) :
    G.girth = n := by
  have he : G.egirth = n := by
    refine le_antisymm ?_ (le_egirth.2 fun b w' hw' => by exact_mod_cast hmin b w' hw')
    rw [← hl]
    exact egirth_le_length hw
  simp [girth, he]

/-- The edge list of `PetersenGraph`, as a list. -/
def petersenEdgesWow : List (Sym2 (Fin 10)) :=
  [s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0),
    s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
    s(5, 7), s(7, 9), s(9, 6), s(6, 8), s(8, 5)]

theorem petersen_adj_iff_wow (a b : Fin 10) :
    PetersenGraph.Adj a b ↔ s(a, b) ∈ petersenEdgesWow ∧ a ≠ b := by
  simp only [fromEdgeSet_adj, Set.mem_insert_iff, Set.mem_singleton_iff, petersenEdgesWow,
    List.mem_cons, List.not_mem_nil, or_false]

/-- Decidable adjacency for `PetersenGraph`, through the explicit edge list. -/
instance petersenDecidableAdjWow : DecidableRel PetersenGraph.Adj := fun a b =>
  decidable_of_iff _ (petersen_adj_iff_wow a b).symm

theorem petersen_no_triangle_wow : ∀ a b c : Fin 10, PetersenGraph.Adj a b →
    PetersenGraph.Adj b c → PetersenGraph.Adj c a → False := by
  decide +kernel

theorem petersen_no_square_wow : ∀ a b c d : Fin 10, PetersenGraph.Adj a b →
    PetersenGraph.Adj b c → PetersenGraph.Adj c d → PetersenGraph.Adj d a → a ≠ c → b ≠ d →
    False := by
  decide +kernel

theorem petersen_girth : PetersenGraph.girth = 5 := by
  have hcyc : (Walk.cons (show PetersenGraph.Adj 0 1 by decide)
      (Walk.cons (show PetersenGraph.Adj 1 2 by decide)
      (Walk.cons (show PetersenGraph.Adj 2 3 by decide)
      (Walk.cons (show PetersenGraph.Adj 3 4 by decide)
      (Walk.cons (show PetersenGraph.Adj 4 0 by decide) Walk.nil))))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  refine girth_eq_of_cycle_wow _ hcyc rfl fun b w hw => ?_
  have h3 := hw.three_le_length
  by_contra hlt
  have : w.length = 3 ∨ w.length = 4 := by omega
  rcases this with hl | hl
  · obtain ⟨c, d, h1, h2, h3⟩ := cycle_len_three_wow w hl
    exact petersen_no_triangle_wow _ _ _ h1 h2 h3
  · obtain ⟨c, d, e, h1, h2, h3, h4, h5, h6⟩ := cycle_len_four_wow w hw hl
    exact petersen_no_square_wow _ _ _ _ h1 h2 h3 h4 h5 h6

end OpenProofs.WrittenOnTheWallII.Test
