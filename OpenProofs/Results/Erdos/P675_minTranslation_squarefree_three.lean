import FormalConjectures.ErdosProblems.«675»

/-!
# `Erdos675.minTranslation_squarefree_three`

Upstream: `Erdos675.minTranslation_squarefree_three` (category test), `FormalConjectures/ErdosProblems/675.lean` line 76.
Proof idea: `t = 4` is a translation for `n = 3` since `1, 2, 3, 5, 6, 7` are all squarefree, so
`sInf ≤ 4`. Every `t ∈ {1, 2, 3}` fails because `4 - t ∈ {1, 2, 3}` is squarefree while `4` is not;
together with `t ≥ 1` this gives `4 ≤ sInf` (the set is nonempty).
-/

open Asymptotics Filter
open Erdos675

namespace OpenProofs.Erdos675

theorem minTranslation_squarefree_three : minTranslation {m : ℕ | Squarefree m} 3 = 4 := by
  have h4 : IsTranslation {m : ℕ | Squarefree m} 3 4 := by
    refine ⟨by norm_num, fun a ha1 ha3 => ?_⟩
    interval_cases a <;> simp only [Set.mem_ofPred_eq] <;> decide +kernel
  have hn4 : ¬ Squarefree 4 := fun h => by simpa using h 2 (by norm_num)
  apply le_antisymm
  · exact Nat.sInf_le h4
  · refine le_csInf ⟨4, h4⟩ fun t ht => ?_
    obtain ⟨ht1, ht⟩ := ht
    by_contra hlt
    push Not at hlt
    have h := ht (4 - t) (by omega) (by omega)
    have he : 4 - t + t = 4 := by omega
    rw [he] at h
    apply hn4
    refine h.mp ?_
    interval_cases t <;> simp only [Set.mem_ofPred_eq] <;> decide +kernel

end OpenProofs.Erdos675
