import FormalConjectures.ErdosProblems.«1193»

/-!
# Erdős 1193: the "trivially no" parts

Upstream: `Erdos1193.erdos_1193.variants.sumRep_univ`, `Erdos1193.erdos_1193.parts.i`,
`Erdos1193.erdos_1193.parts.ii`, `Erdos1193.erdos_1193.variants.upper_density_pos`.
As the upstream docstring notes, taking `A = ℕ` gives `1_A ∗ 1_A (n) = n + 1`, so with
`g n = n + 1` the set `{n | 1_A ∗ 1_A (n) = g n}` is all of `ℕ`, which has density `1`.
This answers both questions negatively and gives positive upper density. The questions are
trivial as recorded in [Er80]; Erdős presumably intended extra restrictions.
-/

open Erdos1193 AdditiveCombinatorics

namespace OpenProofs.Erdos1193

theorem erdos_1193.variants.sumRep_univ (n : ℕ) : sumRep (Set.univ : Set ℕ) n = n + 1 := by
  simp

/-- With `A = ℕ` and `g n = n + 1`, the representation set is everything. -/
theorem setOf_sumRep_univ_eq_univ_P1193 :
    {n : ℕ | sumRep (Set.univ : Set ℕ) n = n + 1} = Set.univ := by
  ext n
  simp

theorem lowerDensity_univ_P1193 : (Set.univ : Set ℕ).lowerDensity = 1 :=
  Set.HasDensity.univ_nat_hasDensity_one.liminf_eq

theorem upperDensity_univ_P1193 : (Set.univ : Set ℕ).upperDensity = 1 :=
  Set.HasDensity.univ_nat_hasDensity_one.limsup_eq

theorem erdos_1193.parts.i :
    ¬ ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.lowerDensity = 0 := by
  intro h
  have := h Set.univ (fun n => n + 1) (fun a b hab => by simpa using hab) (fun n => by omega)
  rw [setOf_sumRep_univ_eq_univ_P1193, lowerDensity_univ_P1193] at this
  norm_num at this

theorem erdos_1193.parts.ii :
    ¬ ∃ c < (1 : ℝ), ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
      {n : ℕ | sumRep A n = g n}.upperDensity < c := by
  rintro ⟨c, hc, h⟩
  have := h Set.univ (fun n => n + 1) (fun a b hab => by simpa using hab) (fun n => by omega)
  rw [setOf_sumRep_univ_eq_univ_P1193, upperDensity_univ_P1193] at this
  linarith

theorem erdos_1193.variants.upper_density_pos :
    ∃ (A : Set ℕ) (g : ℕ → ℕ), Monotone g ∧ (∀ n, 0 < g n) ∧
      0 < {n : ℕ | sumRep A n = g n}.upperDensity := by
  refine ⟨Set.univ, fun n => n + 1, fun a b hab => by simpa using hab, fun n => Nat.succ_pos n, ?_⟩
  rw [setOf_sumRep_univ_eq_univ_P1193, upperDensity_univ_P1193]
  norm_num

end OpenProofs.Erdos1193
