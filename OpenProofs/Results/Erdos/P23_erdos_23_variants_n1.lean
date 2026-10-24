import FormalConjectures.ErdosProblems.«23»

/-!
# `Erdos23.erdos_23.variants.n1`

Upstream: `Erdos23.erdos_23.variants.n1` (category test), `FormalConjectures/ErdosProblems/23.lean` line 42.
Proof idea: pick a vertex `v` of maximum degree and keep exactly the edges of `G` whose
endpoints are on different sides of the cut (neighbours of `v`) / (non-neighbours of `v`).
This subgraph is bipartite. A removed edge cannot join two neighbours of `v` (triangle-free)
and cannot contain `v`, so it lies among the `4 - deg v` non-neighbours of `v`. Two distinct
removed edges would give a vertex of degree at least `2` (if they share a vertex) or at least
`1` (if disjoint) among those non-neighbours, forcing `deg v` that large and producing six
distinct vertices in `Fin 5`.
-/

open SimpleGraph BigOperators
open Erdos23

namespace OpenProofs.Erdos23

theorem erdos23n1_six_distinct (a b c d e f : Fin 5) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (h4 : a ≠ e) (h5 : a ≠ f) (h6 : b ≠ c) (h7 : b ≠ d) (h8 : b ≠ e) (h9 : b ≠ f)
    (h10 : c ≠ d) (h11 : c ≠ e) (h12 : c ≠ f) (h13 : d ≠ e) (h14 : d ≠ f) (h15 : e ≠ f) :
    False := by
  have := List.Nodup.length_le_card (show [a, b, c, d, e, f].Nodup by simp [*])
  simp at this

open scoped Classical in
theorem erdos_23.variants.n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  intro G hG
  obtain ⟨v, -, hv⟩ :=
    Finset.exists_max_image Finset.univ (fun x => G.degree x) Finset.univ_nonempty
  have tri : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False := fun a b c hab hac hbc =>
    hG {a, b, c} (is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)
  let H : SimpleGraph (Fin 5) :=
    { Adj := fun x y => G.Adj x y ∧ ¬(G.Adj v x ↔ G.Adj v y)
      symm := ⟨fun x y h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
      loopless := ⟨fun x h => h.1.ne rfl⟩ }
  refine ⟨H, fun x y h => h.1, ?_, ?_⟩
  · refine ⟨Coloring.mk (fun x => if G.Adj v x then (0 : Fin 2) else 1) ?_⟩
    intro x y h
    have h' : G.Adj x y ∧ ¬(G.Adj v x ↔ G.Adj v y) := h
    by_cases hx : G.Adj v x <;> by_cases hy : G.Adj v y <;> simp_all
  · have inW : ∀ x y, G.Adj x y → ¬H.Adj x y →
        ¬G.Adj v x ∧ ¬G.Adj v y ∧ x ≠ v ∧ y ≠ v := by
      intro x y hxy hH
      have hiff : (G.Adj v x ↔ G.Adj v y) := by
        by_contra hne; exact hH ⟨hxy, hne⟩
      have hx : ¬G.Adj v x := fun hx => tri v x y hx (hiff.1 hx) hxy
      have hy : ¬G.Adj v y := fun hy => hx (hiff.2 hy)
      refine ⟨hx, hy, ?_, ?_⟩
      · rintro rfl; exact hy hxy
      · rintro rfl; exact hx hxy.symm
    have key1 : ∀ p q r, ¬G.Adj v p → ¬G.Adj v q → ¬G.Adj v r → p ≠ v → q ≠ v → r ≠ v →
        G.Adj p q → G.Adj p r → q ≠ r → False := by
      intro p q r hp hq hr hpv hqv hrv hpq hpr hqr
      have h2 : 2 ≤ G.degree p := by
        rw [← card_neighborFinset_eq_degree]
        have hsub : ({q, r} : Finset (Fin 5)) ⊆ G.neighborFinset p := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> simpa
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair hqr] at this
      have h2' : 1 < (G.neighborFinset v).card := by
        rw [card_neighborFinset_eq_degree]; have := hv p (Finset.mem_univ _); omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2'
      rw [mem_neighborFinset] at ha hb
      have hap : a ≠ p := by rintro rfl; exact hp ha
      have haq : a ≠ q := by rintro rfl; exact hq ha
      have har : a ≠ r := by rintro rfl; exact hr ha
      have hbp : b ≠ p := by rintro rfl; exact hp hb
      have hbq : b ≠ q := by rintro rfl; exact hq hb
      have hbr : b ≠ r := by rintro rfl; exact hr hb
      exact erdos23n1_six_distinct v a b p q r ha.ne hb.ne hpv.symm hqv.symm hrv.symm hab
        hap haq har hbp hbq hbr hpq.ne hpr.ne hqr
    have key2 : ∀ p q r s, ¬G.Adj v p → ¬G.Adj v q → ¬G.Adj v r → ¬G.Adj v s →
        p ≠ v → q ≠ v → r ≠ v → s ≠ v → G.Adj p q → G.Adj r s →
        p ≠ r → p ≠ s → q ≠ r → q ≠ s → False := by
      intro p q r s hp hq hr hs hpv hqv hrv hsv hpq hrs hpr hps hqr hqs
      have h1 : 1 ≤ G.degree p := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_pos.2 ⟨q, by simpa⟩
      have h1' : 0 < (G.neighborFinset v).card := by
        rw [card_neighborFinset_eq_degree]; have := hv p (Finset.mem_univ _); omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 h1'
      rw [mem_neighborFinset] at ha
      have hap : a ≠ p := by rintro rfl; exact hp ha
      have haq : a ≠ q := by rintro rfl; exact hq ha
      have har : a ≠ r := by rintro rfl; exact hr ha
      have has : a ≠ s := by rintro rfl; exact hs ha
      exact erdos23n1_six_distinct v a p q r s ha.ne hpv.symm hqv.symm hrv.symm hsv.symm
        hap haq har has hpq.ne hpr hps hqr hqs hrs.ne
    refine Finset.card_le_one.2 fun e1 he1 e2 he2 => ?_
    induction e1 using Sym2.ind with | h x y => ?_
    induction e2 using Sym2.ind with | h x' y' => ?_
    simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet] at he1 he2
    obtain ⟨hxy, hH⟩ := he1
    obtain ⟨hxy', hH'⟩ := he2
    obtain ⟨hx, hy, hxv, hyv⟩ := inW x y hxy hH
    obtain ⟨hx', hy', hxv', hyv'⟩ := inW x' y' hxy' hH'
    rw [Sym2.eq_iff]
    by_contra hne
    push Not at hne
    by_cases h1 : x = x'
    · subst h1
      exact key1 x y y' hx hy hy' hxv hyv hyv' hxy hxy' (hne.1 rfl)
    by_cases h2 : x = y'
    · subst h2
      exact key1 x y x' hx hy hx' hxv hyv hxv' hxy hxy'.symm (hne.2 rfl)
    by_cases h3 : y = x'
    · subst h3
      exact key1 y x y' hy hx hy' hyv hxv hyv' hxy.symm hxy' h2
    by_cases h4 : y = y'
    · subst h4
      exact key1 y x x' hy hx hx' hyv hxv hxv' hxy.symm hxy'.symm h1
    exact key2 x y x' y' hx hy hx' hy' hxv hyv hxv' hyv' hxy hxy' h1 h2 h3 h4

end OpenProofs.Erdos23
