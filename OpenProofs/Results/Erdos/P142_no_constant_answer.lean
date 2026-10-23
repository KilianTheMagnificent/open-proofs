import FormalConjectures.ErdosProblems.«142»

/-!
# Erdős 142: no `k`-independent answer (possible misformalization)

Reference: `OpenProofs.Statements.Erdos142.erdos_142.no_constant_answer` and
`OpenProofs.Statements.Erdos142.erdos_142.variants.isTheta.no_constant_answer`.

Upstream `Erdos142.erdos_142 (k : ℕ)` asks for one `answer : ℕ → ℝ` with `r k ~ answer` for every
`k`. But `r 0 N = N` (upstream `Set.IsAPOfLengthFree.maxCard_zero`) while `r 2 N ≤ 1` (two
distinct points always form a two-term progression), so `N ~ r 2 N`, which is impossible. The
same two values refute the `=Θ` variant.
-/

open Erdos142 Asymptotics Filter

namespace OpenProofs.Erdos142

/-- A subset of `{1, ..., N}` without two-term progressions has at most one element. -/
theorem r_two_le_one_aux142 (N : ℕ) : r 2 N ≤ 1 := by
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

/-- `r 0 N = N`. -/
theorem r_zero_eq_aux142 : (fun N : ℕ => (r 0 N : ℝ)) = fun N : ℕ => (N : ℝ) := by
  funext N
  simp [r, Set.IsAPOfLengthFree.maxCard_zero]

theorem erdos_142.no_constant_answer :
    ∀ g : ℕ → ℝ, ¬ ∀ k : ℕ, (fun N => (r k N : ℝ)) ~[atTop] g := by
  intro g h
  have e : (fun N : ℕ => (N : ℝ)) ~[atTop] (fun N : ℕ => (r 2 N : ℝ)) := by
    have := (h 0).trans (h 2).symm
    rwa [r_zero_eq_aux142] at this
  have ht := e.tendsto_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := (ht.eventually_gt_atTop 1).exists
  have hb : (r 2 N : ℝ) ≤ 1 := by exact_mod_cast r_two_le_one_aux142 N
  exact absurd hb (not_le.2 hN)

end OpenProofs.Erdos142
