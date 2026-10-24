import FormalConjectures.Paper.DegreeSequencesTriangleFree

/-!
# `SimpleGraph.lemma4`

Upstream: `SimpleGraph.lemma4` (category API), `FormalConjectures/Paper/DegreeSequencesTriangleFree.lean` line 274.
Proof idea: put `G` (transported to `ULift (Fin n)`, `n = |α|`) next to an auxiliary bipartite
graph `J₀` and join `v` to one vertex of `J₀` by a single edge. `J₀` has sides
`X = X₁ ⊕ X₂`, `Y = Y₁ ⊕ Y₂` with `|X₁| = 2a`, `|X₂| = b`, `|Y₁| = a`, `|Y₂| = 2b`
(`a = 2n + 1`, `b = 2a`); `X₁ × Y₁` and `X₂ × Y₂` are 1:2 Ferrers blocks, `X₁ × Y₂` and
`X₂ × Y₁` are complete. Degrees: `X₁` takes each value in `[2b+1, 2b+a]` twice, `Y₂` each
value in `[2a+1, 2a+b]` twice (disjoint ranges since `2a ≤ b`), `X₂` values `≡ a (mod 2)` and
`Y₁` values `≡ b (mod 2)` once each (different parities since `a + b` is odd). So every degree
occurs at most three times, `2a + b` occurs exactly three times, and the minimum degree is
`a + 2 ≥ 2n`. The induced graph on the new vertices is isomorphic to `J₀`, the new edge is a
bridge, so `H` stays triangle-free and only the degree of `v` changes (by one).
-/

open BigOperators
open scoped Finset
open SimpleGraph

namespace OpenProofs.SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (d : ℕ → ℕ) (n k r : ℕ)
variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Lemma4Aux

abbrev Xv (a b : ℕ) := Fin (2 * a) ⊕ Fin b
abbrev Yv (a b : ℕ) := Fin a ⊕ Fin (2 * b)
abbrev Wv (a b : ℕ) := Xv a b ⊕ Yv a b

def rel (a b : ℕ) : Xv a b → Yv a b → Prop
  | Sum.inl i, Sum.inl j => (i : ℕ) < 2 * j + 2
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr i, Sum.inr j => (j : ℕ) < 2 * i + 2

def adj (a b : ℕ) : Wv a b → Wv a b → Prop
  | Sum.inl x, Sum.inr y => rel a b x y
  | Sum.inr y, Sum.inl x => rel a b x y
  | _, _ => False

def J0 (a b : ℕ) : SimpleGraph (Wv a b) where
  Adj := adj a b
  symm := ⟨fun u w h => by
    rcases u with u | u <;> rcases w with w | w <;> simp_all [adj]⟩
  loopless := ⟨fun u h => by
    rcases u with u | u <;> simp_all [adj]⟩

lemma deg_eq_sum (a b : ℕ) [DecidableRel (J0 a b).Adj] (w : Wv a b) :
    (J0 a b).degree w = ∑ z, if (J0 a b).Adj w z then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter]

lemma cnt_half (m i : ℕ) : #{j ∈ Finset.range m | i < 2 * j + 2} = m - i / 2 := by
  rw [show ({j ∈ Finset.range m | i < 2 * j + 2} : Finset ℕ) = Finset.Ico (i / 2) m by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega]
  simp

lemma cnt_low (m i : ℕ) (h : i < m) : #{j ∈ Finset.range (2 * m) | j < 2 * i + 2} = 2 * i + 2 := by
  rw [show ({j ∈ Finset.range (2 * m) | j < 2 * i + 2} : Finset ℕ) = Finset.range (2 * i + 2) by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  simp

lemma fin_count (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ j : Fin m, if p j then 1 else 0) = #{j ∈ Finset.range m | p j} := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if p j then 1 else 0) m, Finset.sum_boole]
  simp

lemma deg_X1 (a b : ℕ) [DecidableRel (J0 a b).Adj] (i : Fin (2 * a)) :
    (J0 a b).degree (Sum.inl (Sum.inl i)) = (a - (i : ℕ) / 2) + 2 * b := by
  classical
  rw [deg_eq_sum]
  simp only [Fintype.sum_sum_type]
  simp [J0, adj, rel]
  convert (fin_count a (fun j => (i : ℕ) < 2 * j + 2)).trans (cnt_half a i) <;> congr

lemma deg_X2 (a b : ℕ) [DecidableRel (J0 a b).Adj] (i : Fin b) :
    (J0 a b).degree (Sum.inl (Sum.inr i)) = a + (2 * (i : ℕ) + 2) := by
  classical
  rw [deg_eq_sum]
  simp only [Fintype.sum_sum_type]
  simp [J0, adj, rel]
  convert (fin_count (2 * b) (fun j => j < 2 * (i : ℕ) + 2)).trans (cnt_low b i i.2) <;> congr

lemma deg_Y1 (a b : ℕ) [DecidableRel (J0 a b).Adj] (j : Fin a) :
    (J0 a b).degree (Sum.inr (Sum.inl j)) = (2 * (j : ℕ) + 2) + b := by
  classical
  rw [deg_eq_sum]
  simp only [Fintype.sum_sum_type]
  simp [J0, adj, rel]
  convert (fin_count (2 * a) (fun i => i < 2 * (j : ℕ) + 2)).trans (cnt_low a j j.2) <;> congr

lemma deg_Y2 (a b : ℕ) [DecidableRel (J0 a b).Adj] (j : Fin (2 * b)) :
    (J0 a b).degree (Sum.inr (Sum.inr j)) = 2 * a + (b - (j : ℕ) / 2) := by
  classical
  rw [deg_eq_sum]
  simp only [Fintype.sum_sum_type]
  simp [J0, adj, rel]
  convert (fin_count b (fun i => (j : ℕ) < 2 * i + 2)).trans (cnt_half b j) <;> congr

lemma card_deg_eq (a b : ℕ) [DecidableRel (J0 a b).Adj] (v : ℕ) :
    #{w | (J0 a b).degree w = v} =
      (#{i ∈ Finset.range (2 * a) | (a - i / 2) + 2 * b = v} +
        #{i ∈ Finset.range b | a + (2 * i + 2) = v}) +
      (#{j ∈ Finset.range a | (2 * j + 2) + b = v} +
        #{j ∈ Finset.range (2 * b) | 2 * a + (b - j / 2) = v}) := by
  rw [Finset.card_filter]
  simp only [Fintype.sum_sum_type, deg_X1, deg_X2, deg_Y1, deg_Y2]
  rw [fin_count (2 * a) (fun i => (a - i / 2) + 2 * b = v), fin_count b (fun i => a + (2 * i + 2) = v),
    fin_count a (fun j => (2 * j + 2) + b = v), fin_count (2 * b) (fun j => 2 * a + (b - j / 2) = v)]

lemma count_le (a b v : ℕ) (hab : 2 * a ≤ b) (hpar : (a + b) % 2 = 1) [DecidableRel (J0 a b).Adj] :
    #{w | (J0 a b).degree w = v} ≤ 3 := by
  rw [card_deg_eq]
  have h1 : #{i ∈ Finset.range (2 * a) | (a - i / 2) + 2 * b = v} ≤ 2 := by
    calc _ ≤ #({2 * (a + 2 * b - v), 2 * (a + 2 * b - v) + 1} : Finset ℕ) := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      _ ≤ 2 := Finset.card_le_two
  have h4 : #{j ∈ Finset.range (2 * b) | 2 * a + (b - j / 2) = v} ≤ 2 := by
    calc _ ≤ #({2 * (2 * a + b - v), 2 * (2 * a + b - v) + 1} : Finset ℕ) := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      _ ≤ 2 := Finset.card_le_two
  have h2 : #{i ∈ Finset.range b | a + (2 * i + 2) = v} ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    omega
  have h3 : #{j ∈ Finset.range a | (2 * j + 2) + b = v} ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    omega
  have h14 : #{i ∈ Finset.range (2 * a) | (a - i / 2) + 2 * b = v} = 0 ∨
      #{j ∈ Finset.range (2 * b) | 2 * a + (b - j / 2) = v} = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.1)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.2)
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    omega
  have h23 : #{i ∈ Finset.range b | a + (2 * i + 2) = v} = 0 ∨
      #{j ∈ Finset.range a | (2 * j + 2) + b = v} = 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.1)
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc.2)
    simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    omega
  omega

lemma count_top (a b : ℕ) (ha : 0 < a) (hab : 2 * a ≤ b) (hpar : (a + b) % 2 = 1)
    [DecidableRel (J0 a b).Adj] : #{w | (J0 a b).degree w = 2 * a + b} = 3 := by
  apply le_antisymm (count_le a b _ hab hpar)
  rw [card_deg_eq]
  have h3 : 1 ≤ #{j ∈ Finset.range a | (2 * j + 2) + b = 2 * a + b} := by
    calc 1 = #({a - 1} : Finset ℕ) := by simp
      _ ≤ _ := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_singleton] at hj
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
  have h4 : 2 ≤ #{j ∈ Finset.range (2 * b) | 2 * a + (b - j / 2) = 2 * a + b} := by
    calc 2 = #({0, 1} : Finset ℕ) := by simp
      _ ≤ _ := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
  omega

lemma deg_ge (a b : ℕ) (ha : 0 < a) (hab : 2 * a ≤ b) [DecidableRel (J0 a b).Adj] (w : Wv a b) :
    a + 2 ≤ (J0 a b).degree w := by
  rcases w with (i | i) | (j | j)
  · rw [deg_X1]; have := i.2; omega
  · rw [deg_X2]; omega
  · rw [deg_Y1]; omega
  · rw [deg_Y2]; have := j.2; omega

lemma J0_cliqueFree (a b : ℕ) : (J0 a b).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp [J0, adj] at hxy hxz hyz

/-- Degree-sequence multiplicity is invariant under graph isomorphism. -/
lemma dsm_iso {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {G' : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : G ≃g G') :
    G'.degreeSequenceMultiplicity = G.degreeSequenceMultiplicity := by
  have h : (Finset.univ.val.map fun w => G'.degree w) = Finset.univ.val.map fun v => G.degree v := by
    rw [← Multiset.map_univ_val_equiv e.toEquiv, Multiset.map_map]
    congr 1
    funext x
    exact e.degree_eq x
  unfold degreeSequenceMultiplicity degreeSequence
  rw [h]

lemma dsm_eq_three {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hle : ∀ d, #{x | G.degree x = d} ≤ 3) (x₀ : V) (h₀ : #{x | G.degree x = G.degree x₀} = 3) :
    G.degreeSequenceMultiplicity = 3 := by
  have hc : ∀ d, (G.degreeSequence).count d = #{x | G.degree x = d} := by
    intro d
    rw [degreeSequence, ← Multiset.coe_count, Multiset.sort_eq, Multiset.count_map,
      ← Finset.filter_val, Finset.card_val]
    congr 1
    ext x
    simp [eq_comm]
  have hmem : G.degree x₀ ∈ G.degreeSequence := by
    rw [degreeSequence, Multiset.mem_sort]
    exact Multiset.mem_map.mpr ⟨x₀, Finset.mem_univ _, rfl⟩
  unfold degreeSequenceMultiplicity
  rw [show List.max? ((G.degreeSequence).map fun d => (G.degreeSequence).count d) = some 3 from
    List.max?_eq_some_iff.mpr ⟨?_, ?_⟩]
  · rfl
  · exact List.mem_map.mpr ⟨G.degree x₀, hmem, by rw [hc, h₀]⟩
  · intro n hn
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hn
    rw [hc]
    exact hle d

lemma J0_dsm (a b : ℕ) (ha : 0 < a) (hab : 2 * a ≤ b) (hpar : (a + b) % 2 = 1)
    [DecidableRel (J0 a b).Adj] : (J0 a b).degreeSequenceMultiplicity = 3 := by
  have hb : 0 < b := by omega
  apply dsm_eq_three _ (fun d => count_le a b d hab hpar) (Sum.inr (Sum.inr ⟨0, by omega⟩))
  rw [deg_Y2]
  simpa using count_top a b ha hab hpar

section Ext

variable {γ : Type*} (G : SimpleGraph γ) (v : γ) {W : Type} (J : SimpleGraph W) (u₀ : W)

/-- Adjacency of `G` and `J` side by side, plus the single edge `v — u₀`. -/
def hadj : γ ⊕ W → γ ⊕ W → Prop
  | Sum.inl p, Sum.inl q => G.Adj p q
  | Sum.inr x, Sum.inr y => J.Adj x y
  | Sum.inl p, Sum.inr x => p = v ∧ x = u₀
  | Sum.inr x, Sum.inl p => p = v ∧ x = u₀

def Hg : SimpleGraph (γ ⊕ W) where
  Adj := hadj G v J u₀
  symm := ⟨fun s t h => by
    rcases s with s | s <;> rcases t with t | t <;> simp only [hadj] at h ⊢ <;>
      first | exact h.symm | exact h⟩
  loopless := ⟨fun s h => by
    rcases s with s | s <;> simp only [hadj] at h
    · exact G.irrefl h
    · exact J.irrefl h⟩

lemma Hg_deg_inl [Fintype γ] [Fintype W] [DecidableEq γ] [DecidableRel G.Adj]
    [DecidableRel (Hg G v J u₀).Adj] (p : γ) :
    (Hg G v J u₀).degree (Sum.inl p) = G.degree p + if p = v then 1 else 0 := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
    Finset.card_filter]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    exact if_congr Iff.rfl rfl rfl
  · by_cases hp : p = v
    · subst hp
      simp [Hg, hadj]
    · simp [Hg, hadj, hp]

lemma Hg_cliqueFree (hG : G.CliqueFree 3) (hJ : J.CliqueFree 3) : (Hg G v J u₀).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp only [Hg, hadj] at hxy hxz hyz
  · exact hG _ (is3Clique_iff.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩)
  all_goals first
    | exact hJ _ (is3Clique_iff.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩)
    | simp_all

end Ext

open scoped Classical in
lemma main.{u, w} {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h₁ : G.CliqueFree 3) (v : α) :
    ∃ (β : Type w) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧
      H.degree (i v) = G.degree v + 1 ∧
      (∀ w ≠ v, H.degree (i w) = G.degree w) ∧
      let J := H.induce (Set.compl (Set.range i))
      degreeSequenceMultiplicity J = 3 ∧ J.minDegree ≥ 2 * Fintype.card α := by
  classical
  set N := Fintype.card α with hN
  set a := 2 * N + 1 with ha
  set b := 2 * a with hb
  have ha0 : 0 < a := by omega
  have hab : 2 * a ≤ b := by omega
  have hpar : (a + b) % 2 = 1 := by omega
  let e : α ≃ ULift.{w} (Fin N) := (Fintype.equivFin α).trans Equiv.ulift.symm
  let G' : SimpleGraph (ULift.{w} (Fin N)) := G.comap e.symm
  have hG' : G'.CliqueFree 3 := by
    intro t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
    exact h₁ _ (is3Clique_iff.mpr ⟨e.symm x, e.symm y, e.symm z, hxy, hxz, hyz, rfl⟩)
  have hdeg' : ∀ x, G'.degree (e x) = G.degree x := by
    intro x
    have h := (Iso.comap e.symm G).degree_eq (e x)
    have h2 : (Iso.comap e.symm G) (e x) = x := e.symm_apply_apply x
    rw [h2] at h
    convert h.symm using 1
  let u₀ : Wv a b := Sum.inl (Sum.inl ⟨0, by omega⟩)
  let H := Hg G' (e v) (J0 a b) u₀
  let i : G ↪g H :=
    { toFun := fun x => Sum.inl (e x)
      inj' := fun x y h => e.injective (Sum.inl_injective h)
      map_rel_iff' := by
        intro x y
        change G.Adj (e.symm (e x)) (e.symm (e y)) ↔ G.Adj x y
        simp }
  refine ⟨ULift.{w} (Fin N) ⊕ Wv a b, inferInstance, H, inferInstance, i, ?_, ?_, ?_, ?_⟩
  · exact Hg_cliqueFree G' (e v) (J0 a b) u₀ hG' (J0_cliqueFree a b)
  · show H.degree (Sum.inl (e v)) = _
    rw [Hg_deg_inl, hdeg']
    simp
  · intro x hx
    show H.degree (Sum.inl (e x)) = _
    rw [Hg_deg_inl, hdeg']
    simp [hx]
  · intro J
    have hmem : ∀ x : Wv a b, (Sum.inr x : ULift.{w} (Fin N) ⊕ Wv a b) ∈ Set.compl (Set.range i) := by
      rintro x ⟨y, hy⟩
      exact Sum.inl_ne_inr hy
    let σ : Wv a b → ↥(Set.compl (Set.range i)) := fun x => ⟨Sum.inr x, hmem x⟩
    have hσ : Function.Bijective σ := by
      refine ⟨fun x y h => Sum.inr_injective (congrArg Subtype.val h), ?_⟩
      rintro ⟨z | z, hz⟩
      · refine absurd ⟨e.symm z, ?_⟩ hz
        change Sum.inl (e (e.symm z)) = Sum.inl z
        rw [e.apply_symm_apply]
      · exact ⟨z, rfl⟩
    let iso : J0 a b ≃g J :=
      { toEquiv := Equiv.ofBijective σ hσ
        map_rel_iff' := by
          intro x y
          simp [J, H, Hg, hadj, σ] }
    refine ⟨?_, ?_⟩
    · rw [dsm_iso iso]
      exact J0_dsm a b ha0 hab hpar
    · have : Nonempty ↥(Set.compl (Set.range i)) := ⟨σ u₀⟩
      apply le_minDegree_of_forall_le_degree
      intro z
      obtain ⟨x, rfl⟩ := hσ.2 z
      have h1 := iso.degree_eq x
      have h2 := deg_ge a b ha0 hab x
      have h3 : J.degree (σ x) = (J0 a b).degree x := h1
      omega

end Lemma4Aux

open scoped Classical in
theorem lemma4 (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn: G.Connected)
    (h₁ : G.CliqueFree 3) (v : α) :
    ∃ (β : Type*) (_ : Fintype β) (H : SimpleGraph β) (_ : DecidableRel H.Adj) (i : G ↪g H),
      H.CliqueFree 3 ∧
      H.degree (i v) = G.degree v + 1 ∧
      (∀ w ≠ v, H.degree (i w) = G.degree w) ∧
      let J := H.induce (Set.compl (Set.range i))
      degreeSequenceMultiplicity J = 3 ∧ J.minDegree ≥ 2 * Fintype.card α := by
  exact Lemma4Aux.main G h₁ v

end OpenProofs.SimpleGraph
