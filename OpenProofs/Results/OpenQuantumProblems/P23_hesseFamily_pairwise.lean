import FormalConjectures.OpenQuantumProblems.«23»
import OpenProofs.Results.OpenQuantumProblems.P23_hasSICPOVM_three

/-!
# `OpenQuantumProblem23.hesseFamily_pairwise`

Upstream: `OpenQuantumProblem23.hesseFamily_pairwise` (category test), `FormalConjectures/OpenQuantumProblems/23.lean` line 296.
Proof idea: this is exactly the pairwise-overlap half of our already checked
`hasSICPOVM_three` result, `OpenProofs.OpenQuantumProblem23.hesse3_pairwise`
(`P23_hasSICPOVM_three.lean`): `normSq z = 1/4` from `conj z * z = 1/4`, then `fin_cases` on
both indices with `rfl` lemmas for each family member, `conj ω = ω ^ 2`, and `grind` from
`s ^ 2 = 1/2` and `ω ^ 2 + ω + 1 = 0`.
-/

open OpenQuantumProblem23

namespace OpenProofs.OpenQuantumProblem23

theorem hesseFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 3) hesseFamily :=
  hesse3_pairwise

end OpenProofs.OpenQuantumProblem23
