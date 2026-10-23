import FormalConjectures.ErdosProblems.«409»

/-!
# Erdős 409 (i): no `n`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos409.erdos_409.parts.i.no_constant_answer`.

Upstream `Erdos409.erdos_409.parts.i (n : ℕ) (hn : 0 < n)` asserts that one constant is the least
number of iterations of `n ↦ φ n + 1` reaching a prime, for every `n > 0`. For `n = 2` (prime) the
least number is `0`; for `n = 1` it is not `0`, since `1` is not prime.
-/

open scoped ArithmeticFunction.sigma Nat

namespace OpenProofs.Erdos409

theorem erdos_409.parts.i.no_constant_answer :
    ∀ a : ℕ, ¬ ∀ n : ℕ, 0 < n → IsLeast { i | (φ · + 1)^[i] n |>.Prime } a := by
  intro a h
  have h2 := (h 2 (by norm_num)).2 (show 0 ∈ { i | (φ · + 1)^[i] 2 |>.Prime } by
    simpa using Nat.prime_two)
  have h1 := (h 1 (by norm_num)).1
  have ha : a = 0 := by simpa using h2
  subst ha
  simp at h1

end OpenProofs.Erdos409
