import FormalConjectures.ErdosProblems.«640»

/-!
# `Erdos640.erdos_640.variants.three`

Upstream: `Erdos640.erdos_640.variants.three` (category textbook), `FormalConjectures/ErdosProblems/640.lean` line 55.
Proof idea: a graph that is not 2-colourable has a closed walk of odd length
(`two_colorable_iff_forall_loop_even`). By induction on a walk `a → b` we get either an odd
cycle or a path `a → b` of the same length parity: prepend the first edge `a ~ c` to the path
`q : c → b`; if `a` already lies on `q`, split `q = q₁ ++ q₂` at `a`; then `a ~ c` followed by
`q₁` is a cycle (a path `c → a` containing the edge `ac` has length 1), which is odd when `q₁`
has even length, and otherwise `q₂` has the right parity. A path `u → u` is trivial, so an odd
closed walk yields an odd cycle. Lifting that cycle to the subgraph induced on its support keeps
it an odd closed walk there, so the induced subgraph has chromatic number at least 3.
-/

open SimpleGraph
open Erdos640

namespace OpenProofs.Erdos640

/-- A path `c → a` that uses the edge `ac` has length 1. -/
theorem path_length_one_of_mem_edges_e640 {V : Type*} {G : SimpleGraph V} :
    ∀ {c a : V} (q : G.Walk c a), q.IsPath → s(a, c) ∈ q.edges → q.length = 1
  | _, _, .nil, _, he => by simp at he
  | c, a, .cons (v := d) h q, hp, he => by
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, -⟩
      · subst h1 h2
        exact absurd h (G.irrefl)
      · subst h1
        rw [Walk.length_cons, Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hp.1)]
    · exact absurd (q.snd_mem_support_of_mem_edges he) hp.2

/-- Every walk yields an odd cycle or a path with the same endpoints and length parity. -/
theorem oddCycle_or_path_e640 {V : Type*} {G : SimpleGraph V} :
    ∀ {a b : V} (p : G.Walk a b),
      (∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ Odd c.length) ∨
        ∃ q : G.Walk a b, q.IsPath ∧ (Even q.length ↔ Even p.length)
  | _, _, .nil => Or.inr ⟨.nil, by simp⟩
  | a, b, .cons (v := c) h p => by
    rcases oddCycle_or_path_e640 p with hc | ⟨q, hq, hpar⟩
    · exact Or.inl hc
    by_cases ha : a ∈ q.support
    · obtain ⟨q₁, q₂, hq₁, hq₂, rfl⟩ := hq.mem_support_iff_exists_append.mp ha
      rw [Walk.length_append] at hpar
      by_cases he : Even q₁.length
      · left
        refine ⟨a, .cons h q₁, ?_, ?_⟩
        · refine (Walk.cons_isCycle_iff q₁ h).mpr ⟨hq₁, fun hm => ?_⟩
          have := path_length_one_of_mem_edges_e640 q₁ hq₁ hm
          rw [this] at he
          exact absurd he (by decide)
        · rw [Walk.length_cons]
          exact he.add_one
      · right
        refine ⟨q₂, hq₂, ?_⟩
        rw [Walk.length_cons]
        rw [Nat.even_add] at hpar
        rw [Nat.even_add_one, ← hpar]
        tauto
    · right
      refine ⟨.cons h q, (Walk.cons_isPath_iff h q).mpr ⟨hq, ha⟩, ?_⟩
      simp only [Walk.length_cons, Nat.even_add_one, hpar]

theorem erdos_640.variants.three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (3 : ℕ∞) ≤ G.chromaticNumber) : HasHighChromaticOddCycle G 3 := by
  have hnc : ¬ G.Colorable 2 := by
    intro hc
    have h2 := hc.chromaticNumber_le
    have : (3 : ℕ∞) ≤ 2 := hG.trans (by exact_mod_cast h2)
    exact absurd this (by decide)
  rw [two_colorable_iff_forall_loop_even] at hnc
  push Not at hnc
  obtain ⟨u, w, hw⟩ := hnc
  rcases oddCycle_or_path_e640 w with ⟨v, c, hc, hodd⟩ | ⟨q, hq, hpar⟩
  · refine ⟨v, c, hc, hodd, ?_⟩
    let c' := c.induce {x | x ∈ c.support} (fun x hx => hx)
    have hlen : c'.length = c.length := by
      rw [← Walk.length_map (Embedding.induce _).toHom c']
      exact congrArg Walk.length (Walk.map_induce c _)
    have h3 := c'.three_le_chromaticNumber_of_odd_loop (by rw [hlen]; exact hodd)
    exact_mod_cast h3
  · rw [Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hq)] at hpar
    exact absurd (hpar.mp (by simp)) hw

end OpenProofs.Erdos640
