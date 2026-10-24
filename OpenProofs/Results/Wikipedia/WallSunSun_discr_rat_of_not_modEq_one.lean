import FormalConjectures.Wikipedia.WallSunSun

/-!
# `QuadraticAlgebra.discr_rat_of_not_modEq_one`

Upstream: `QuadraticAlgebra.discr_rat_of_not_modEq_one` (category textbook), `FormalConjectures/Wikipedia/WallSunSun.lean` line 44.
Proof idea: for squarefree `d ≢ 1 (mod 4)` the ring of integers of `ℚ(√d)` is `ℤ[√d]`.
If `x = r + s√d` is integral over `ℤ`, so is its conjugate, hence `A = 2r` and
`N = r² - d s²` are integers. Then `(2ds)² = d (A² - 4N)`, so `2ds` is an integer `k`
with `d ∣ k²`, hence `d ∣ k` (squarefree) and `B = 2s` is an integer with
`A² - d B² = 4N`. Since `d ≡ 2, 3 (mod 4)`, checking residues mod 4 forces `A, B` even,
so `r, s ∈ ℤ`. This gives a ring isomorphism `ℤ[√d] ≃+* 𝓞 ℚ(√d)`; transporting the basis
`1, √d` and using invariance of `Algebra.discr` under algebra isomorphisms reduces the claim
to the trace matrix `!![2, 0; 0, 2d]` of `ℤ[√d]`, whose determinant is `4d`.
-/

open Algebra (IsQuadraticExtension)
open NumberField
open QuadraticAlgebra

namespace OpenProofs.QuadraticAlgebra

/-- The inclusion `ℤ[√d] → ℚ(√d)`. -/
def wssIncl (d : ℤ) : QuadraticAlgebra ℤ d 0 →+* QuadraticAlgebra ℚ d 0 where
  toFun z := ⟨z.re, z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

lemma wssIncl_injective (d : ℤ) : Function.Injective (wssIncl d) := by
  intro z w h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [wssIncl] at h1 h2
  ext <;> assumption

lemma wssDiscr_int (d : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (d : ℤ) (0 : ℤ)) = 4 * d := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℤ) (0 : ℤ)), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.coe_ofEquivFun, QuadraticAlgebra.basis]
  ring

lemma wssMod4 {d A B N : ℤ} (hd : d % 4 = 2 ∨ d % 4 = 3) (h : A ^ 2 - d * B ^ 2 = 4 * N) :
    2 ∣ A ∧ 2 ∣ B := by
  have key : (A ^ 2 - d * B ^ 2) % 4 = 0 := by rw [h]; simp
  have hA : A % 4 = 0 ∨ A % 4 = 1 ∨ A % 4 = 2 ∨ A % 4 = 3 := by omega
  have hB : B % 4 = 0 ∨ B % 4 = 1 ∨ B % 4 = 2 ∨ B % 4 = 3 := by omega
  rcases hA with hA | hA | hA | hA <;> rcases hB with hB | hB | hB | hB <;>
    rcases hd with hd | hd <;>
    simp [pow_two, Int.sub_emod, Int.mul_emod, hA, hB, hd] at key <;> omega

lemma wssSqfree_mod4 {d : ℤ} (hsq : Squarefree d) (hd₄ : ¬ d ≡ 1 [ZMOD 4]) :
    d % 4 = 2 ∨ d % 4 = 3 := by
  have h4 : ¬ (2 * 2 : ℤ) ∣ d := fun h => by
    have := hsq 2 h
    rw [Int.isUnit_iff] at this
    omega
  rw [Int.ModEq] at hd₄
  omega

lemma wssIntRat {q : ℚ} (h : IsIntegral ℤ q) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

lemma wssIntegral_algebraMap {d : ℤ} {q : ℚ}
    (h : IsIntegral ℤ (algebraMap ℚ (QuadraticAlgebra ℚ d 0) q)) : ∃ n : ℤ, (n : ℚ) = q :=
  wssIntRat ((isIntegral_algebraMap_iff (QuadraticAlgebra.algebraMap_injective)).mp h)

lemma wssSurj {d : ℤ} (hsq : Squarefree d) (hd₄ : ¬ d ≡ 1 [ZMOD 4])
    (x : QuadraticAlgebra ℚ d 0) (hx : IsIntegral ℤ x) : ∃ z, wssIncl d z = x := by
  have hstar : IsIntegral ℤ (star x) := by
    simpa [starRingEnd_apply] using hx.map (starRingEnd (QuadraticAlgebra ℚ d 0)).toIntAlgHom
  have hsum : x + star x = algebraMap ℚ _ (2 * x.re) := by
    ext <;> simp; ring
  have hprod : x * star x = algebraMap ℚ _ (x.re ^ 2 - d * x.im ^ 2) := by
    rw [QuadraticAlgebra.algebraMap_eq]
    ext <;> simp <;> ring
  obtain ⟨A, hA⟩ := wssIntegral_algebraMap (hsum ▸ hx.add hstar)
  obtain ⟨N, hN⟩ := wssIntegral_algebraMap (hprod ▸ hx.mul hstar)
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hy : ((d : ℚ) * (2 * x.im)) ^ 2 = ((d * (A ^ 2 - 4 * N) : ℤ) : ℚ) := by
    push_cast; rw [hA, hN]; ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℚ) = d * (2 * x.im) := by
    apply wssIntRat
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hy]
    exact isIntegral_algebraMap
  have hk2 : k ^ 2 = d * (A ^ 2 - 4 * N) := by
    have h' : ((k ^ 2 : ℤ) : ℚ) = ((d * (A ^ 2 - 4 * N) : ℤ) : ℚ) := by
      rw [← hy, Int.cast_pow, hk]
    exact Int.cast_injective h'
  obtain ⟨B, hB⟩ : d ∣ k := (hsq.dvd_pow_iff_dvd two_ne_zero).mp ⟨_, hk2⟩
  have hBs : (B : ℚ) = 2 * x.im := by
    have : (d : ℚ) * B = d * (2 * x.im) := by rw [← hk, hB]; push_cast; ring
    exact mul_left_cancel₀ (by exact_mod_cast hd0) this
  have hrel : A ^ 2 - d * B ^ 2 = 4 * N := by
    have : (A : ℚ) ^ 2 - d * (B : ℚ) ^ 2 = 4 * N := by rw [hA, hBs, hN]; ring
    exact_mod_cast this
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := wssMod4 (wssSqfree_mod4 hsq hd₄) hrel
  refine ⟨⟨a, b⟩, ?_⟩
  ext
  · simp [wssIncl]; push_cast at hA; linarith
  · simp [wssIncl]; push_cast at hBs; linarith

lemma wssIncl_isIntegral {d : ℤ} (z : QuadraticAlgebra ℤ d 0) : IsIntegral ℤ (wssIncl d z) :=
  (Algebra.IsIntegral.isIntegral z).map (wssIncl d).toIntAlgHom

/-- The inclusion `ℤ[√d] → 𝓞 ℚ(√d)`. -/
def wssToO (d : ℤ) [Fact <| Squarefree d] [Fact <| d ≠ 1] :
    QuadraticAlgebra ℤ d 0 →+* 𝓞 (QuadraticAlgebra ℚ d 0) where
  toFun := RingOfIntegers.restrict (wssIncl d) wssIncl_isIntegral
  map_one' := by simp only [RingOfIntegers.restrict, map_one]; rfl
  map_mul' z w := by simp only [RingOfIntegers.restrict, map_mul]; rfl
  map_zero' := by simp only [RingOfIntegers.restrict, map_zero]; rfl
  map_add' z w := by simp only [RingOfIntegers.restrict, map_add]; rfl

variable {d : ℤ} [Fact <| Squarefree d] [Fact <| d ≠ 1]

lemma wssToO_bijective (hd₄ : ¬ d ≡ 1 [ZMOD 4]) : Function.Bijective (wssToO d) := by
  refine ⟨fun z w h => wssIncl_injective d ?_, fun y => ?_⟩
  · exact congrArg (fun t : 𝓞 (QuadraticAlgebra ℚ d 0) => (t : QuadraticAlgebra ℚ d 0)) h
  · obtain ⟨z, hz⟩ := wssSurj (Fact.out : Squarefree d) hd₄ (y : QuadraticAlgebra ℚ d 0)
      (RingOfIntegers.isIntegral_coe y)
    exact ⟨z, RingOfIntegers.ext hz⟩

theorem discr_rat_of_not_modEq_one (hd₄ : ¬ d ≡ 1 [ZMOD 4]) :
    discr (QuadraticAlgebra ℚ d 0) = 4 * d := by
  let e := (RingEquiv.ofBijective _ (wssToO_bijective hd₄)).toIntAlgEquiv
  rw [← NumberField.discr_eq_discr _ ((QuadraticAlgebra.basis (d : ℤ) (0 : ℤ)).map e.toLinearEquiv),
    Module.Basis.coe_map, ← wssDiscr_int d]
  exact (Algebra.discr_eq_discr_of_algEquiv _ e).symm

end OpenProofs.QuadraticAlgebra
