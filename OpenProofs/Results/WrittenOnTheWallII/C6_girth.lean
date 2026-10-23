import FormalConjectures.WrittenOnTheWallII.Test
import OpenProofs.Results.WrittenOnTheWallII.Petersen_girth

/-!
# Written on the Wall II tests: `C6_girth`

Upstream: `WrittenOnTheWallII.Test.C6_girth` (category test): `C6.girth = 6`, where
`C6 = cycleGraph 6`.

The walk `0-1-2-3-4-5-0` is a cycle of length `6`, so the girth is at most `6`. Kernel `decide`
shows `cycleGraph 6` has no closed adjacency chain of length `3` or `5` (it is bipartite) and no
chain `a ~ b ~ c ~ d ~ a` with `a ≠ c` and `b ≠ d`. With the walk lemmas from the
`petersen_girth` result, every cycle has length at least `6`, so `girth = 6`.
-/

open WrittenOnTheWallII.Test SimpleGraph

namespace OpenProofs.WrittenOnTheWallII.Test

theorem c6_no_triangle_wow : ∀ a b c : Fin 6, C6.Adj a b → C6.Adj b c → C6.Adj c a → False := by
  decide +kernel

theorem c6_no_square_wow : ∀ a b c d : Fin 6, C6.Adj a b → C6.Adj b c → C6.Adj c d →
    C6.Adj d a → a ≠ c → b ≠ d → False := by
  decide +kernel

theorem c6_no_pentagon_wow : ∀ a b c d e : Fin 6, C6.Adj a b → C6.Adj b c → C6.Adj c d →
    C6.Adj d e → C6.Adj e a → False := by
  decide +kernel

theorem C6_girth : C6.girth = 6 := by
  have hcyc : (Walk.cons (show C6.Adj 0 1 by decide)
      (Walk.cons (show C6.Adj 1 2 by decide)
      (Walk.cons (show C6.Adj 2 3 by decide)
      (Walk.cons (show C6.Adj 3 4 by decide)
      (Walk.cons (show C6.Adj 4 5 by decide)
      (Walk.cons (show C6.Adj 5 0 by decide) Walk.nil)))))).IsCycle := by
    rw [Walk.isCycle_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.isTrail_def]; decide
    · simp
    · decide
  refine girth_eq_of_cycle_wow _ hcyc rfl fun b w hw => ?_
  have h3 := hw.three_le_length
  by_contra hlt
  have : w.length = 3 ∨ w.length = 4 ∨ w.length = 5 := by omega
  rcases this with hl | hl | hl
  · obtain ⟨c, d, h1, h2, h3⟩ := cycle_len_three_wow w hl
    exact c6_no_triangle_wow _ _ _ h1 h2 h3
  · obtain ⟨c, d, e, h1, h2, h3, h4, h5, h6⟩ := cycle_len_four_wow w hw hl
    exact c6_no_square_wow _ _ _ _ h1 h2 h3 h4 h5 h6
  · obtain ⟨c, d, e, f, h1, h2, h3, h4, h5⟩ := cycle_len_five_wow w hl
    exact c6_no_pentagon_wow _ _ _ _ _ h1 h2 h3 h4 h5

end OpenProofs.WrittenOnTheWallII.Test
