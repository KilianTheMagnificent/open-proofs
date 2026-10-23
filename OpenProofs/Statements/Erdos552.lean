import FormalConjectures.ErdosProblems.«552»

/-!
# Answer-free negation of Erdős 552 (possible misformalization)

Upstream `Erdos552.erdos_552.parts.i : ∀ n, graphRamsey C₄ K_{1,n} = erdos_552.parts.i.answer`
uses one constant `answer : ℕ` for every `n`, while `R(C₄, S_n)` depends on `n` (the same file
notes `R(C₄, S_0) = 1` and `R(C₄, S_1) = 4`). The statement below is the upstream body with the
placeholder replaced by a universally quantified `a`.
-/

namespace OpenProofs.Statements.Erdos552

/-- `R(C₄, K_{1,n})` is not constant in `n`. -/
theorem erdos_552.parts.i.no_constant_answer : ∀ a : ℕ, ¬ ∀ (n : ℕ),
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
      (completeBipartiteGraph (Fin 1) (Fin n)) = a := by
  sorry

end OpenProofs.Statements.Erdos552
