import FormalConjectures.OpenQuantumProblems.«23»

/-!
# `OpenQuantumProblem23.hasSICPOVM_two`

Upstream: `OpenQuantumProblem23.hasSICPOVM_two` (category test), `FormalConjectures/OpenQuantumProblems/23.lean` line 279.
Proof idea: the witness is upstream's tetrahedral family `qubitSICFamily`; normalization is
upstream's `qubitSICFamily_normalized`. For the pairwise overlaps, `normSq z = 1/3` follows from
`conj z * z = 1/3` in `ℂ`. After `fin_cases` on both indices, each overlap is a polynomial in
`a = tetraA`, `b = tetraB` and `ω`, with `conj ω = ω ^ 2`; `grind`'s ring solver closes the
identity from `a ^ 2 = 1/3`, `b ^ 2 = 2/3` and `ω ^ 2 + ω + 1 = 0`. The family is unfolded through
`rfl` lemmas per index (unfolding the definition by `simp` would realize a match splitter in this
module, which the checker rejects).
-/

open OpenQuantumProblem23

namespace OpenProofs.OpenQuantumProblem23

theorem qubit2_omega_star : star ω = ω ^ 2 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [ω, pow_two, Complex.mul_re]
    linear_combination (1 / 4 : ℝ) * h3
  · simp [ω, pow_two, Complex.mul_im]
    ring

theorem qubit2_omega_conj : (starRingEnd ℂ) ω = ω ^ 2 := qubit2_omega_star

theorem qubit2_omega_sq : ω ^ 2 + ω + 1 = 0 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [ω, pow_two, Complex.mul_re]
    linear_combination (-1 / 4 : ℝ) * h3
  · simp [ω, pow_two, Complex.mul_im]
    ring

theorem qubit2_a_sq : (tetraA : ℂ) ^ 2 = 1 / 3 := by
  rw [← Complex.ofReal_pow, tetraA, Real.sq_sqrt (by norm_num)]
  push_cast; ring

theorem qubit2_b_sq : (tetraB : ℂ) ^ 2 = 2 / 3 := by
  rw [← Complex.ofReal_pow, tetraB, Real.sq_sqrt (by norm_num)]
  push_cast; ring

theorem qubit2_normSq_eq {z : ℂ} (h : star z * z = 1 / 3) : Complex.normSq z = 1 / 3 := by
  have h2 : ((Complex.normSq z : ℝ) : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    exact h
  exact_mod_cast h2

theorem qubit2_at0 : qubitSICFamily 0 = vec2 1 0 := rfl
theorem qubit2_at1 : qubitSICFamily 1 = vec2 (tetraA : ℂ) (tetraB : ℂ) := rfl
theorem qubit2_at2 : qubitSICFamily 2 = vec2 (tetraA : ℂ) ((tetraB : ℂ) * ω) := rfl
theorem qubit2_at3 : qubitSICFamily 3 = vec2 (tetraA : ℂ) ((tetraB : ℂ) * (ω ^ 2)) := rfl

theorem qubit2_pairwise : HasConstantOverlapSq (sicOverlapSq 2) qubitSICFamily := by
  have hω := qubit2_omega_sq
  have ha := qubit2_a_sq
  have hb := qubit2_b_sq
  intro i j hij
  rw [sicOverlapSq_two]
  apply qubit2_normSq_eq
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [qubit2_at0, qubit2_at1, qubit2_at2, qubit2_at3,
      vec2, mkStateVector, Fin.sum_univ_two, qubit2_omega_conj] <;>
    grind

theorem hasSICPOVM_two : HasSICPOVM 2 :=
  ⟨qubitSICFamily, qubitSICFamily_normalized, qubit2_pairwise⟩

end OpenProofs.OpenQuantumProblem23
