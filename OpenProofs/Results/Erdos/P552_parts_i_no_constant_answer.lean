import FormalConjectures.ErdosProblems.«552»

/-!
# Erdős 552 (i): no `n`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos552.erdos_552.parts.i.no_constant_answer`.

Upstream `Erdos552.erdos_552.parts.i` asserts `∀ n, R(C₄, K_{1,n}) = answer` for one constant.
But `R(C₄, K_{1,0}) = 1` (one vertex suffices to embed the one-vertex graph `K_{1,0}`, and zero
vertices do not), while `R(C₄, K_{1,1}) ≠ 1` (on one vertex neither `C₄` nor an edge `K_{1,1}`
fits).
-/

namespace OpenProofs.Erdos552

/-- A copy of a graph needs at least as many vertices as the graph has. -/
theorem card_le_of_isContained_aux552 {α β : Type} [Fintype α] [Fintype β]
    {G : SimpleGraph α} {H : SimpleGraph β} (hGH : G.IsContained H) :
    Fintype.card α ≤ Fintype.card β := by
  obtain ⟨f⟩ := hGH
  exact Fintype.card_le_of_injective f f.injective

theorem erdos_552.parts.i.no_constant_answer : ∀ a : ℕ, ¬ ∀ (n : ℕ),
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
      (completeBipartiteGraph (Fin 1) (Fin n)) = a := by
  intro a h
  have r0 : SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
      (completeBipartiteGraph (Fin 1) (Fin 0)) = 1 := by
    have one_mem : (1 : ℕ) ∈ {n : ℕ | ∀ (C : SimpleGraph (Fin n)),
        (SimpleGraph.cycleGraph 4).IsContained C ∨
        (completeBipartiteGraph (Fin 1) (Fin 0)).IsContained Cᶜ} := by
      intro C
      right
      refine ⟨⟨⟨fun _ => 0, fun {x y} hxy => ?_⟩, fun x y _ => ?_⟩⟩
      · rcases x with x | x <;> rcases y with y | y
        · simp at hxy
        · exact y.elim0
        · exact x.elim0
        · exact x.elim0
      · rcases x with x | x <;> rcases y with y | y
        · simp [Subsingleton.elim x y]
        · exact y.elim0
        · exact x.elim0
        · exact x.elim0
    unfold SimpleGraph.graphRamsey
    apply le_antisymm (Nat.sInf_le one_mem)
    apply le_csInf ⟨1, one_mem⟩
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · exfalso
      rcases hm ⊥ with hc | hc
      · have := card_le_of_isContained_aux552 hc
        simp at this
      · have := card_le_of_isContained_aux552 hc
        simp at this
    · exact hm'
  have r1 : SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
      (completeBipartiteGraph (Fin 1) (Fin 1)) ≠ 1 := by
    intro hr
    unfold SimpleGraph.graphRamsey at hr
    have hne : {n : ℕ | ∀ (C : SimpleGraph (Fin n)), (SimpleGraph.cycleGraph 4).IsContained C ∨
        (completeBipartiteGraph (Fin 1) (Fin 1)).IsContained Cᶜ}.Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc, Nat.sInf_empty] at hr
      exact absurd hr (by norm_num)
    have hmem := Nat.sInf_mem hne
    rw [hr] at hmem
    rcases hmem ⊥ with hc | hc
    · have := card_le_of_isContained_aux552 hc
      simp at this
    · have := card_le_of_isContained_aux552 hc
      simp at this
  exact r1 ((h 1).trans ((h 0).symm.trans r0))

end OpenProofs.Erdos552
