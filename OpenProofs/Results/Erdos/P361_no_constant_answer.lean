import FormalConjectures.ErdosProblems.«361»

/-!
# Erdős 361: no `c`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos361.erdos_361.no_constant_answer`.

Upstream `Erdos361.erdos_361 (c : ℝ) (hc : 0 < c)` asserts that `subsetSumAvoidanceNumber c` is
the same function of `n` for every `c > 0`. At `n = 2`: for `c = 1/4` the range is
`{1, ..., ⌊1/2⌋} = ∅`, giving `0`; for `c = 1` the range is `{1, 2}` and `{1}` avoids the sum `2`,
giving `1`.
-/

open Erdos361

namespace OpenProofs.Erdos361

theorem erdos_361.no_constant_answer :
    ∀ a : ℕ → ℕ, ¬ ∀ c : ℝ, 0 < c → subsetSumAvoidanceNumber c = a := by
  intro a h
  have e1 := congrFun (h (1 / 4) (by norm_num)) 2
  have e2 := congrFun (h 1 (by norm_num)) 2
  have f1 : ⌊(1 / 4 : ℝ) * (2 : ℕ)⌋₊ = 0 := by norm_num [Nat.floor_eq_zero]
  have f2 : ⌊(1 : ℝ) * (2 : ℕ)⌋₊ = 2 := by norm_num
  simp only [subsetSumAvoidanceNumber, f1, f2] at e1 e2
  have c1 : maxSubsetSumAvoidingCard 0 2 = 0 := by decide
  have c2 : maxSubsetSumAvoidingCard 2 2 = 1 := by decide
  omega

end OpenProofs.Erdos361
