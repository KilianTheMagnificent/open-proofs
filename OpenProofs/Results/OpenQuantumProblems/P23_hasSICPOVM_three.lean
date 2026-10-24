import FormalConjectures.OpenQuantumProblems.«23»

/-!
# `OpenQuantumProblem23.hasSICPOVM_three`

Upstream: `OpenQuantumProblem23.hasSICPOVM_three` (category test), `FormalConjectures/OpenQuantumProblems/23.lean` line 301.
Proof idea: the witness is upstream's Hesse family `hesseFamily`; normalization is upstream's
`hesseFamily_normalized`. For the pairwise overlaps, `normSq z = 1/4` follows from
`conj z * z = 1/4` in `ℂ`. After `fin_cases` on both indices, each overlap is a polynomial in
`s = hesseS` and `ω`, with `conj ω = ω ^ 2`; `grind`'s ring solver closes the identity from
`s ^ 2 = 1/2` and `ω ^ 2 + ω + 1 = 0`.
-/

open OpenQuantumProblem23

namespace OpenProofs.OpenQuantumProblem23

theorem hesse3_omega_star : star ω = ω ^ 2 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [ω, pow_two, Complex.mul_re]
    linear_combination (1 / 4 : ℝ) * h3
  · simp [ω, pow_two, Complex.mul_im]
    ring

theorem hesse3_omega_conj : (starRingEnd ℂ) ω = ω ^ 2 := hesse3_omega_star

theorem hesse3_omega_sq : ω ^ 2 + ω + 1 = 0 := by
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  apply Complex.ext
  · simp [ω, pow_two, Complex.mul_re]
    linear_combination (-1 / 4 : ℝ) * h3
  · simp [ω, pow_two, Complex.mul_im]
    ring

theorem hesse3_s_sq : (hesseS : ℂ) ^ 2 = 1 / 2 := by
  rw [← Complex.ofReal_pow, hesseS, Real.sq_sqrt (by norm_num)]
  push_cast; ring

theorem hesse3_normSq_eq {z : ℂ} (h : star z * z = 1 / 4) : Complex.normSq z = 1 / 4 := by
  have h2 : ((Complex.normSq z : ℝ) : ℂ) = ((1 / 4 : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    push_cast
    exact h
  exact_mod_cast h2

theorem hesse3_at0 : hesseFamily 0 = vec3 0 (hesseS : ℂ) (-(hesseS : ℂ)) := rfl
theorem hesse3_at1 : hesseFamily 1 = vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * ω)) := rfl
theorem hesse3_at2 : hesseFamily 2 = vec3 0 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2))) := rfl
theorem hesse3_at3 : hesseFamily 3 = vec3 (-(hesseS : ℂ)) 0 (hesseS : ℂ) := rfl
theorem hesse3_at4 : hesseFamily 4 = vec3 (-((hesseS : ℂ) * ω)) 0 (hesseS : ℂ) := rfl
theorem hesse3_at5 : hesseFamily 5 = vec3 (-((hesseS : ℂ) * (ω ^ 2))) 0 (hesseS : ℂ) := rfl
theorem hesse3_at6 : hesseFamily 6 = vec3 (hesseS : ℂ) (-(hesseS : ℂ)) 0 := rfl
theorem hesse3_at7 : hesseFamily 7 = vec3 (hesseS : ℂ) (-((hesseS : ℂ) * ω)) 0 := rfl
theorem hesse3_at8 : hesseFamily 8 = vec3 (hesseS : ℂ) (-((hesseS : ℂ) * (ω ^ 2))) 0 := rfl

theorem hesse3_pairwise : HasConstantOverlapSq (sicOverlapSq 3) hesseFamily := by
  have hω := hesse3_omega_sq
  have hs := hesse3_s_sq
  intro i j hij
  rw [sicOverlapSq_three]
  apply hesse3_normSq_eq
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [hesse3_at0, hesse3_at1, hesse3_at2, hesse3_at3, hesse3_at4, hesse3_at5, hesse3_at6, hesse3_at7, hesse3_at8,
      vec3, mkStateVector, Fin.sum_univ_three, hesse3_omega_conj] <;>
    grind

theorem hasSICPOVM_three : HasSICPOVM 3 :=
  ⟨hesseFamily, hesseFamily_normalized, hesse3_pairwise⟩

end OpenProofs.OpenQuantumProblem23
