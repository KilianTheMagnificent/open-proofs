import FormalConjectures.ErdosProblems.«902»

/-!
# Erdős 902: `erdos_902.variants.f_two`

Upstream: `Erdos902.erdos_902.variants.f_two`. The upper bound `f 2 ≤ 7` is upstream's
`f_two_le`; membership of `7` in the defining set reuses Erdős's tournament on `Fin 7`
(`a → a + 1, a + 2, a + 4`). For the lower bound, let `G` be a tournament on `m ≥ 2`
vertices with property `S_2` and fix a vertex `v`. For every `u ≠ v` the pair `{u, v}` is
dominated by some `x ∉ {u, v}`, which then lies in the in-neighbourhood `I(v)` and beats `u`.
So `I(v)` is nonempty and each of its elements is beaten by another element of `I(v)`;
following this twice from `a ∈ I(v)` gives `b → a` and `c → b` in `I(v)` with `c ≠ a`
(else `a → b → a`), so `|I(v)| ≥ 3`. Summing in- and out-degrees gives
`2 * ∑ indeg + m ≤ m * m`, hence `7 * m ≤ m * m` and `m ≥ 7`.
-/

open Erdos902

namespace OpenProofs.Erdos902

theorem indeg_ge_three_of_propertyS2 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (hG : G.IsTournament) (hS : HasPropertyS G 2) (hV : 2 ≤ Fintype.card V)
    (v : V) : 3 ≤ ∑ x, if G.Adj x v then 1 else 0 := by
  rw [← Finset.card_filter]
  have key : ∀ u, u ≠ v → ∃ x, x ≠ u ∧ G.Adj x u ∧ G.Adj x v := by
    intro u huv
    obtain ⟨x, hx, hadj⟩ := hS {u, v} (Finset.card_pair huv)
    refine ⟨x, fun h => hx (by simp [h]), hadj u (by simp), hadj v (by simp)⟩
  have hne : ∀ x, G.Adj x v → x ≠ v := fun x hx h => hG.1 v (h ▸ hx)
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 hV
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨a, -, -, ha⟩ := key u hu
  obtain ⟨b, hba, hb_a, hb⟩ := key a (hne a ha)
  obtain ⟨c, hcb, hc_b, hc⟩ := key b (hne b hb)
  have hca : c ≠ a := by
    intro h
    rw [h] at hc_b
    exact (hG.2 b a hba).1 hb_a hc_b
  have hsub : ({a, b, c} : Finset V) ⊆ Finset.univ.filter fun x => G.Adj x v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  have hcard : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, c, hba.symm, hca.symm, hcb.symm, rfl⟩
  exact hcard ▸ Finset.card_le_card hsub

theorem card_ge_seven_of_propertyS2 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (hG : G.IsTournament) (hS : HasPropertyS G 2)
    (hV : 2 ≤ Fintype.card V) : 7 ≤ Fintype.card V := by
  set m := Fintype.card V with hm
  have hpt : ∀ v x : V, ((if G.Adj x v then 1 else 0) + (if G.Adj v x then 1 else 0) +
      (if x = v then 1 else 0) : ℕ) ≤ 1 := by
    intro v x
    by_cases hxv : x = v
    · subst hxv
      simp [hG.1]
    · have := hG.2 x v hxv
      by_cases h : G.Adj x v <;> simp_all
  have hdeg : ∀ v : V, (∑ x, if G.Adj x v then 1 else 0) + (∑ x, if G.Adj v x then 1 else 0) + 1
      ≤ m := by
    intro v
    calc (∑ x, if G.Adj x v then 1 else 0) + (∑ x, if G.Adj v x then 1 else 0) + 1
        = ∑ x, ((if G.Adj x v then 1 else 0) + (if G.Adj v x then 1 else 0) +
            (if x = v then 1 else 0) : ℕ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
      _ ≤ ∑ _x : V, 1 := Finset.sum_le_sum fun x _ => hpt v x
      _ = m := by simp [hm]
  have hsum : ∑ v : V, ((∑ x, if G.Adj x v then 1 else 0) +
      (∑ x, if G.Adj v x then 1 else 0) + 1) ≤ m * m := by
    calc _ ≤ ∑ _v : V, m := Finset.sum_le_sum fun v _ => hdeg v
      _ = m * m := by simp [hm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_comm (f := fun v x => if G.Adj v x then 1 else 0)] at hsum
  have h3 : 3 * m ≤ ∑ v : V, ∑ x, if G.Adj x v then 1 else 0 := by
    calc 3 * m = ∑ _v : V, 3 := by simp [hm, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v _ => indeg_ge_three_of_propertyS2 G hG hS hV v
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  have hm0 : 0 < m := by omega
  nlinarith

theorem erdos_902.variants.f_two : f 2 = 7 := by
  refine le_antisymm f_two_le (le_csInf ⟨7, ?_⟩ ?_)
  · refine ⟨by norm_num, ⟨fun a b => b - a ∈ ({1, 2, 4} : Finset (Fin 7))⟩,
      ⟨by decide, by decide⟩, ?_⟩
    intro E hE
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hE
    have key : ∀ a b : Fin 7, a ≠ b → ∃ x, x ≠ a ∧ x ≠ b ∧
        a - x ∈ ({1, 2, 4} : Finset (Fin 7)) ∧ b - x ∈ ({1, 2, 4} : Finset (Fin 7)) := by
      decide
    obtain ⟨x, hxa, hxb, ha, hb⟩ := key a b hab
    refine ⟨x, by simp [hxa, hxb], fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ha
    · rw [Finset.mem_singleton.1 he]
      exact hb
  · rintro m ⟨hm, G, hG, hS⟩
    classical
    simpa using card_ge_seven_of_propertyS2 G hG hS (by simpa using hm)

end OpenProofs.Erdos902
