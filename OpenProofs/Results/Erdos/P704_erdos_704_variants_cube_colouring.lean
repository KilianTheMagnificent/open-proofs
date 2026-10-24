import FormalConjectures.ErdosProblems.«704»

/-!
# `Erdos704.erdos_704.variants.cube_colouring`

Upstream: `Erdos704.erdos_704.variants.cube_colouring` (category textbook), `FormalConjectures/ErdosProblems/704.lean` line 91.
Proof idea: let `t = √n` and `M = ⌈t⌉₊ + 1`. Colour `x` by `i ↦ ⌊x i * t⌋ mod M`, i.e. tile
`ℝⁿ` by half-open cubes of side `1/√n` and colour the cubes periodically with period `M`.
If two points get the same colour and all floors agree, every coordinate differs by less than
`1/√n`, so the distance is `< 1`. Otherwise some floor difference is a nonzero multiple of `M`,
so that coordinate differs by more than `(M - 1)/√n ≥ 1`, and the distance is `> 1`. This uses
`M ^ n ≤ (2 + √n) ^ n` colours.
-/

open Filter
open scoped Topology
open Erdos704

namespace OpenProofs.Erdos704

theorem erdos_704.variants.cube_colouring :
    ∀ n : ℕ, ∃ k : ℕ, (unitDistanceGraph n).Colorable k ∧
      (k : ℝ) ≤ (2 + Real.sqrt n) ^ n := by
  intro n
  set t : ℝ := Real.sqrt n with ht
  set M : ℕ := ⌈t⌉₊ + 1 with hM
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htt : t * t = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have hceil : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  let C : (unitDistanceGraph n).Coloring (Fin n → ZMod M) :=
    SimpleGraph.Coloring.mk (fun x i => ((⌊x i * t⌋ : ℤ) : ZMod M)) (by
      intro x y hxy heq
      have hd : dist x y = 1 := hxy
      rw [EuclideanSpace.dist_eq] at hd
      have hS : ∑ i, (x i - y i) ^ 2 = 1 := by
        have h0 : 0 ≤ ∑ i, dist (x i) (y i) ^ 2 := by positivity
        have := (Real.sqrt_eq_one).1 hd
        simpa [Real.dist_eq, sq_abs] using this
      have hcong : ∀ i, (M : ℤ) ∣ ⌊y i * t⌋ - ⌊x i * t⌋ := by
        intro i
        have := congrFun heq i
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this
      by_cases hall : ∀ i, ⌊x i * t⌋ = ⌊y i * t⌋
      · have hlt : ∀ i, (x i - y i) ^ 2 * n < 1 := by
          intro i
          have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (hall i)
          have h2 : (x i * t - y i * t) ^ 2 < 1 := by
            have := abs_lt.1 h1
            nlinarith [abs_nonneg (x i * t - y i * t)]
          have : (x i * t - y i * t) ^ 2 = (x i - y i) ^ 2 * n := by
            rw [← htt]; ring
          linarith
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          simp at hS
        · have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hn⟩⟩
          have := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlt i)
          rw [← Finset.sum_mul, hS] at this
          simp at this
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨c, hc⟩ := hcong i
        have hc0 : c ≠ 0 := by
          rintro rfl
          apply hi
          omega
        have hle : (x i - y i) ^ 2 ≤ 1 := by
          rw [← hS]
          exact Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have hfx := Int.floor_le (x i * t)
        have hfx' := Int.lt_floor_add_one (x i * t)
        have hfy := Int.floor_le (y i * t)
        have hfy' := Int.lt_floor_add_one (y i * t)
        have htpos : 0 < t := by
          rcases ht0.lt_or_eq with h | h
          · exact h
          · exfalso; apply hi; rw [← h]; simp
        have hcR : ((⌊y i * t⌋ : ℤ) : ℝ) - ⌊x i * t⌋ = (M : ℝ) * c := by
          exact_mod_cast hc
        have hMR : (M : ℝ) = ⌈t⌉₊ + 1 := by simp [hM]
        rcases lt_or_gt_of_ne hc0 with hneg | hpos
        · have : (c : ℝ) ≤ -1 := by exact_mod_cast (show c ≤ -1 by omega)
          have h3 : (y i - x i) * t < -t := by nlinarith
          have h4 : y i - x i < -1 := by
            by_contra h5; push Not at h5; nlinarith
          nlinarith
        · have : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
          have h3 : (y i - x i) * t > t := by nlinarith
          have h4 : y i - x i > 1 := by
            by_contra h5; push Not at h5; nlinarith
          nlinarith)
  refine ⟨_, C.colorable, ?_⟩
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hMR : (M : ℝ) = ⌈t⌉₊ + 1 := by simp [hM]
  rw [Nat.cast_pow]
  apply pow_le_pow_left₀ (by positivity)
  have := Nat.ceil_lt_add_one ht0
  linarith

end OpenProofs.Erdos704
