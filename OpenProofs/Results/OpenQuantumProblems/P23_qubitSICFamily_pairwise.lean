import FormalConjectures.OpenQuantumProblems.«23»
import OpenProofs.Results.OpenQuantumProblems.P23_hasSICPOVM_two

/-!
# `OpenQuantumProblem23.qubitSICFamily_pairwise`

Upstream: `OpenQuantumProblem23.qubitSICFamily_pairwise` (category test), `FormalConjectures/OpenQuantumProblems/23.lean` line 274.
Proof idea: this is exactly the pairwise-overlap half of our already checked
`hasSICPOVM_two` result, `OpenProofs.OpenQuantumProblem23.qubit2_pairwise`
(`P23_hasSICPOVM_two.lean`): `normSq z = 1/3` from `conj z * z = 1/3`, then `fin_cases` on
both indices with `rfl` lemmas for each family member, `conj ω = ω ^ 2`, and `grind` from
`a ^ 2 = 1/3`, `b ^ 2 = 2/3` and `ω ^ 2 + ω + 1 = 0`.
-/

open OpenQuantumProblem23

namespace OpenProofs.OpenQuantumProblem23

theorem qubitSICFamily_pairwise :
    HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily :=
  qubit2_pairwise

end OpenProofs.OpenQuantumProblem23
