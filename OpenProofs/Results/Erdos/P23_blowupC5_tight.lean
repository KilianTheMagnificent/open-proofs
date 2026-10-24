import FormalConjectures.ErdosProblems.«23»

/-!
# `Erdos23.blowupC5_tight`

Upstream: `Erdos23.blowupC5_tight` (category test), `FormalConjectures/ErdosProblems/23.lean` line 112.
Proof idea: fix a proper 2-colouring `C` of `H`. Every choice `(a₀,…,a₄)` of one vertex per part
spans a 5-cycle of `blowupC5 n`, which has a `C`-monochromatic edge; each edge between consecutive
parts lies in `n ^ 3` such cycles, so double counting gives `n ^ 5 ≤ n ^ 3 * m`, where `m` counts
triples `(i, a, b)` with `C (i, a) = C (i + 1, b)`. These triples inject into the edges of
`blowupC5 n` that are monochromatic, hence not in `H`, giving `n ^ 2 ≤ m ≤ card`. (`hH` is unused.)
-/

open SimpleGraph BigOperators
open Erdos23

namespace OpenProofs.Erdos23

/-- Every 2-colouring of a 5-cycle has a monochromatic edge. -/
lemma blowupC5Tight_five_cycle (x0 x1 x2 x3 x4 : Fin 2) :
    (1 : ℕ) ≤ (if x0 = x1 then 1 else 0) + (if x1 = x2 then 1 else 0)
      + (if x2 = x3 then 1 else 0) + (if x3 = x4 then 1 else 0) + (if x4 = x0 then 1 else 0) := by
  revert x0 x1 x2 x3 x4
  decide

lemma blowupC5Tight_count (n : ℕ) (c0 c1 c2 c3 c4 : Fin n → Fin 2) :
    n ^ 5 ≤ n ^ 3 * ((∑ a, ∑ b, if c0 a = c1 b then 1 else 0)
      + (∑ a, ∑ b, if c1 a = c2 b then 1 else 0) + (∑ a, ∑ b, if c2 a = c3 b then 1 else 0)
      + (∑ a, ∑ b, if c3 a = c4 b then 1 else 0) + (∑ a, ∑ b, if c4 a = c0 b then 1 else 0)) := by
  calc n ^ 5 = ∑ _a0 : Fin n, ∑ _a1 : Fin n, ∑ _a2 : Fin n, ∑ _a3 : Fin n, ∑ _a4 : Fin n,
        (1 : ℕ) := by simp; ring
    _ ≤ ∑ a0, ∑ a1, ∑ a2, ∑ a3, ∑ a4, ((if c0 a0 = c1 a1 then 1 else 0)
          + (if c1 a1 = c2 a2 then 1 else 0) + (if c2 a2 = c3 a3 then 1 else 0)
          + (if c3 a3 = c4 a4 then 1 else 0) + (if c4 a4 = c0 a0 then 1 else 0)) := by
        gcongr with a0 _ a1 _ a2 _ a3 _ a4 _
        exact blowupC5Tight_five_cycle _ _ _ _ _
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
        have hc : (∑ a, ∑ b, if c4 a = c0 b then 1 else 0 : ℕ)
            = ∑ b, ∑ a, if c4 a = c0 b then 1 else 0 := Finset.sum_comm
        simp only [← Finset.mul_sum, hc]
        ring

open scoped Classical in
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  obtain ⟨C⟩ := hBip
  set T := (Finset.univ : Finset (ZMod 5 × Fin n × Fin n)).filter
    (fun t => C (t.1, t.2.1) = C (t.1 + 1, t.2.2)) with hT
  have hcard : T.card = ∑ i : ZMod 5, ∑ a : Fin n, ∑ b : Fin n,
      if C (i, a) = C (i + 1, b) then 1 else 0 := by
    rw [hT, Finset.card_filter]
    simp only [Fintype.sum_prod_type]
  have h5 : n ^ 5 ≤ n ^ 3 * T.card := by
    rw [hcard, show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have key := blowupC5Tight_count n (fun a => C (0, a)) (fun a => C (1, a)) (fun a => C (2, a))
      (fun a => C (3, a)) (fun a => C (4, a))
    have e0 : (0 : ZMod 5) + 1 = 1 := by decide
    have e1 : (1 : ZMod 5) + 1 = 2 := by decide
    have e2 : (2 : ZMod 5) + 1 = 3 := by decide
    have e3 : (3 : ZMod 5) + 1 = 4 := by decide
    have e4 : (4 : ZMod 5) + 1 = 0 := by decide
    simp only [e0, e1, e2, e3, e4]
    beta_reduce at key
    linarith
  have h2 : n ^ 2 ≤ T.card := by
    by_contra h
    replace h := not_le.mp h
    have : n ^ 3 * T.card < n ^ 3 * n ^ 2 := Nat.mul_lt_mul_of_pos_left h (by positivity)
    have : n ^ 3 * n ^ 2 = n ^ 5 := by ring
    omega
  refine h2.trans (Finset.card_le_card_of_injOn (fun t => s((t.1, t.2.1), (t.1 + 1, t.2.2)))
    ?_ ?_)
  · rintro ⟨i, a, b⟩ ht
    simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, mem_edgeFinset, mem_edgeSet]
    refine ⟨?_, fun hadj => C.valid hadj ht⟩
    simp only [blowupC5, fromRel_adj]
    refine ⟨fun h => ?_, Or.inl (Or.inl trivial)⟩
    have hne : ∀ j : ZMod 5, j ≠ j + 1 := by decide
    exact hne i (congrArg Prod.fst h)
  · rintro ⟨i, a, b⟩ _ ⟨j, a', b'⟩ _ h
    simp only [Sym2.eq_iff, Prod.mk.injEq] at h
    have hne2 : ∀ k : ZMod 5, k + 1 + 1 ≠ k := by decide
    rcases h with ⟨⟨rfl, rfl⟩, -, rfl⟩ | ⟨⟨rfl, -⟩, h2, -⟩
    · rfl
    · exact absurd h2 (hne2 j)

end OpenProofs.Erdos23
