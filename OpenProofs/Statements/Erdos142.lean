import FormalConjectures.ErdosProblems.«142»

/-!
# Answer-free negations of Erdős 142 (possible misformalization)

Upstream `Erdos142.erdos_142 (k : ℕ) : (fun N => (r k N : ℝ)) ~[atTop] erdos_142.answer` and
`Erdos142.erdos_142.variants.isTheta` use one function `answer : ℕ → ℝ` of `N` alone for every
`k`, while the informal problem asks for `f_k` depending on `k`. Since `r 0 N = N` and
`r 2 N ≤ 1`, no single function works. The statements below are the upstream bodies with the
placeholder `answer` replaced by a universally quantified `g` (the placeholder definition itself
cannot appear in a checked statement, since its body is a placeholder).
-/

open Erdos142 Asymptotics Filter

namespace OpenProofs.Statements.Erdos142

/-- No single `g : ℕ → ℝ` is asymptotic to `r k` for every `k`. -/
theorem erdos_142.no_constant_answer :
    ∀ g : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (r k N : ℝ)) ~[atTop] g := by
  sorry

/-- No single `g : ℕ → ℝ` has the order of magnitude of `r k` for every `k`. -/
theorem erdos_142.variants.isTheta.no_constant_answer :
    ∀ g : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (r k N : ℝ)) =Θ[atTop] g := by
  sorry

end OpenProofs.Statements.Erdos142
