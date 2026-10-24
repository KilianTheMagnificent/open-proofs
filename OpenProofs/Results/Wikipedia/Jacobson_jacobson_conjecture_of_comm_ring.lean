import FormalConjectures.Wikipedia.Jacobson

/-!
# `Jacobson.jacobson_conjecture_of_comm_ring`

Upstream: `Jacobson.jacobson_conjecture_of_comm_ring` (category textbook), `FormalConjectures/Wikipedia/Jacobson.lean` line 58.
Proof idea: Krull's intersection theorem. In a commutative ring the Jacobson radical (the
intersection of all maximal ideals) lies in `Ideal.jacobson ⊥`, so
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` with `M = R` gives `⨅ n, J ^ n • ⊤ = ⊥`, i.e.
`⨅ n, J ^ n = 0`.
-/

open Ring
open Jacobson

universe u

namespace OpenProofs.Jacobson

theorem jacobson_conjecture_of_comm_ring (R : Type u) [CommRing R] [IsNoetherianRing R] :
    JacobsonConjectureFor R := by
  unfold JacobsonConjectureFor
  have h : Ring.jacobson R ≤ Ideal.jacobson ⊥ := by
    rw [Ring.jacobson_eq_sInf_isMaximal, Ideal.jacobson]
    exact sInf_le_sInf fun J hJ => hJ.2
  have := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) _ h
  simpa using this

end OpenProofs.Jacobson
