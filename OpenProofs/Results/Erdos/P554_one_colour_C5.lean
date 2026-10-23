import FormalConjectures.ErdosProblems.«554»

/-!
# Erdős 554: `multicolourGraphRamsey_one_cycleGraph_five`

Upstream: `Erdos554.multicolourGraphRamsey_one_cycleGraph_five` (category test).

With one colour, every edge of `⊤` on `Fin n` gets the colour `0` (`Fin 1` is a subsingleton),
so the colour-`0` label graph is `⊤` itself. By `isContained_top_iff`, `cycleGraph 5 ⊑ ⊤` on
`Fin n` holds iff `Fin 5` embeds into `Fin n`, i.e. iff `5 ≤ n`. The defining set of
`multicolourGraphRamsey 1 (cycleGraph 5)` is therefore `Set.Ici 5`, whose infimum is `5`.
-/

open Erdos554 SimpleGraph

namespace OpenProofs.Erdos554

/-- With a single colour, the colour-`0` label graph of any labelling of `⊤` is `⊤`. -/
theorem labelGraph_fin_one_eq_top_P554 {n : ℕ} (C : TopEdgeLabeling (Fin n) (Fin 1)) :
    C.labelGraph 0 = ⊤ := by
  ext x y
  simp only [TopEdgeLabeling.labelGraph_adj, top_adj]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Subsingleton.elim _ _⟩⟩

/-- Membership in the defining set of `multicolourGraphRamsey 1 (cycleGraph 5)`. -/
theorem mem_iff_P554 (n : ℕ) :
    (∀ C : TopEdgeLabeling (Fin n) (Fin 1), ∃ i, (cycleGraph 5).IsContained (C.labelGraph i)) ↔
      5 ≤ n := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h default
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    rw [labelGraph_fin_one_eq_top_P554] at hi
    obtain ⟨f⟩ := isContained_top_iff.1 hi
    simpa using Fintype.card_le_of_embedding f
  · intro hn C
    refine ⟨0, ?_⟩
    rw [labelGraph_fin_one_eq_top_P554]
    exact isContained_top_iff.2 ⟨Fin.castLEEmb hn⟩

theorem multicolourGraphRamsey_one_cycleGraph_five :
    multicolourGraphRamsey 1 (cycleGraph 5) = 5 := by
  unfold multicolourGraphRamsey
  simp only [mem_iff_P554]
  exact csInf_Ici

end OpenProofs.Erdos554
