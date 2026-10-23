import FormalConjectures.ErdosProblems.«142»

/-!
# Erdős 142, `=Θ` variant: no `k`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos142.erdos_142.variants.isTheta.no_constant_answer`.

Upstream `Erdos142.erdos_142.variants.isTheta (k : ℕ)` asks for one `answer : ℕ → ℝ` with
`r k =Θ answer` for every `k`. But `r 0 N = N` (upstream `Set.IsAPOfLengthFree.maxCard_zero`)
and `r 2 N ≤ 1` (two distinct points always form a two-term progression), so a common `g` would
give `N = O(1)`.
-/

open Erdos142 Asymptotics Filter

namespace OpenProofs.Erdos142

/-- A subset of `{1, ..., N}` without two-term progressions has at most one element. -/
theorem r_two_le_one_aux142t (N : ℕ) : r 2 N ≤ 1 := by
  apply csSup_le'
  rintro x ⟨S, -, hS, rfl⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hlt
  rcases lt_or_gt_of_ne hab with h | h
  · have := hS {a, b} (by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption) (Nat.isAPOfLength_pair h)
    norm_num at this
  · have := hS {b, a} (by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption) (Nat.isAPOfLength_pair h)
    norm_num at this

theorem erdos_142.variants.isTheta.no_constant_answer :
    ∀ g : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (r k N : ℝ)) =Θ[atTop] g := by
  intro g h
  have h0 : (fun N : ℕ => (r 0 N : ℝ)) = fun N : ℕ => (N : ℝ) := by
    funext N
    simp [r, Set.IsAPOfLengthFree.maxCard_zero]
  have e : (fun N : ℕ => (N : ℝ)) =O[atTop] (fun N : ℕ => (r 2 N : ℝ)) := by
    have := ((h 0).trans (h 2).symm).isBigO
    rwa [h0] at this
  have e2 : (fun N : ℕ => (N : ℝ)) =O[atTop] (fun _ => (1 : ℝ)) := by
    refine e.trans (IsBigO.of_bound 1 (Eventually.of_forall fun N => ?_))
    simp only [Real.norm_natCast, norm_one, one_mul]
    exact_mod_cast r_two_le_one_aux142t N
  obtain ⟨c, hc⟩ := e2.bound
  obtain ⟨N, hN⟩ := (hc.and (eventually_gt_atTop ⌈c⌉₊)).exists
  have h1 := hN.1
  simp only [Real.norm_natCast, norm_one, mul_one] at h1
  have h2 : (⌈c⌉₊ : ℝ) < N := by exact_mod_cast hN.2
  linarith [Nat.le_ceil c]

end OpenProofs.Erdos142
