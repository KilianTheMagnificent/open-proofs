import FormalConjectures.Wikipedia.BorsukConjecture

/-!
# `Borsuk.borsuk_conjecture.zero`

Upstream: `Borsuk.borsuk_conjecture.zero` (category test), `FormalConjectures/Wikipedia/BorsukConjecture.lean` line 173.
Proof idea: `ℝ^0` is a subsingleton (functions on `Fin 0`), so no subset of it is
nontrivial and the hypothesis `s.Nontrivial` is contradictory.
-/

open Metric Bornology
open scoped EuclideanGeometry
open Borsuk

namespace OpenProofs.Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

theorem borsuk_conjecture.zero : BorsukConjecture 0 := by
  intro s _ hs
  exact absurd hs (Set.subsingleton_of_subsingleton).not_nontrivial

end OpenProofs.Borsuk
