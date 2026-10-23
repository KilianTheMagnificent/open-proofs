import FormalConjectures.ErdosProblems.«629»
import Mathlib.Combinatorics.Hall.Basic

/-!
# Erdős 629: `erdos_629.variants.n_two`

Upstream: `Erdos629.erdos_629.variants.n_two`, i.e. `n 2 = 6` (Erdős, Rubin and Taylor 1980),
where `n k` is the least number of vertices of a `2`-colourable graph on `Fin m` whose list
chromatic number exceeds `k`.

Upper bound (`n_two_le_six_P629`): `K_{3,3}` on `Fin 6` is `2`-colourable but not
`k`-choosable for `k ≤ 2`; for `k = 2` both sides get the lists `{1,2}, {1,3}, {2,3}`, and the
finite case check is done by `omega`. It is `6`-choosable (Hall's theorem gives an injective
choice from lists of size `6`), so its list chromatic number is a genuine infimum and is `≥ 3`.

Lower bound (`six_le_n_two_P629`): every `2`-colourable graph on `m ≤ 5` vertices is
`2`-choosable. One colour class `A` has at most two vertices. If `|A| ≤ 1`, colour `A` from its
lists; every other vertex keeps a colour outside that one colour. If `|A| = 2`, the other side
has at most three vertices; pick `x₁ ∈ L a₁`, `x₂ ∈ L a₂` such that no list on the other side is
contained in `{x₁, x₂}` (a common colour works when the lists meet; otherwise the four pairs
`{x₁, x₂}` are distinct two-sets and each other-side list rules out at most one of them).
-/

open Erdos629

namespace OpenProofs.Erdos629

open SimpleGraph

/-- Every graph on a finite vertex type `V` is `card V`-choosable (injective choice by Hall). -/
theorem isKChoosable_card_P629 {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.IsKChoosable (Fintype.card V) := by
  classical
  intro L hL
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion L).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · calc s.card ≤ Fintype.card V := Finset.card_le_univ s
        _ = (L v).card := (hL v).symm
        _ ≤ (s.biUnion L).card := Finset.card_le_card (Finset.subset_biUnion_of_mem L hv)
  obtain ⟨f, hf, hfL⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective L).1 hall
  exact ⟨Coloring.mk f fun {u v} huv heq => G.ne_of_adj huv (hf heq), hfL⟩

/-- `K_{3,3}` on `Fin 6`: sides `{0,1,2}` and `{3,4,5}`. -/
def K33_P629 : SimpleGraph (Fin 6) where
  Adj u v := (u.val < 3 ∧ 3 ≤ v.val) ∨ (v.val < 3 ∧ 3 ≤ u.val)
  symm := ⟨fun u v h => by omega⟩
  loopless := ⟨fun u h => by omega⟩

instance decidableRelAdj_K33_P629 : DecidableRel K33_P629.Adj := fun u v => by
  unfold K33_P629; infer_instance

theorem K33_colorable_P629 : K33_P629.Colorable 2 :=
  ⟨Coloring.mk (fun v => if v.val < 3 then 0 else 1) fun {u v} huv heq => by
    simp only [K33_P629] at huv
    split_ifs at heq <;> simp_all; omega⟩

theorem K33_not_choosable_P629 (k : ℕ) (hk : k ≤ 2) : ¬ K33_P629.IsKChoosable k := by
  intro h
  interval_cases k
  · obtain ⟨C, hC⟩ := h (fun _ => ∅) (fun _ => rfl)
    simpa using hC 0
  · obtain ⟨C, hC⟩ := h (fun _ => {0}) (fun _ => rfl)
    have h0 := hC 0
    have h3 := hC 3
    simp only [Finset.mem_singleton] at h0 h3
    exact C.valid (show K33_P629.Adj 0 3 by decide) (h0.trans h3.symm)
  · let L : Fin 6 → Finset ℕ := ![{1, 2}, {1, 3}, {2, 3}, {1, 2}, {1, 3}, {2, 3}]
    obtain ⟨C, hC⟩ := h L (by decide)
    have h0 : C 0 = 1 ∨ C 0 = 2 := by simpa [L] using hC 0
    have h1 : C 1 = 1 ∨ C 1 = 3 := by simpa [L] using hC 1
    have h2 : C 2 = 2 ∨ C 2 = 3 := by simpa [L] using hC 2
    have h3 : C 3 = 1 ∨ C 3 = 2 := by simpa [L] using hC 3
    have h4 : C 4 = 1 ∨ C 4 = 3 := by simpa [L] using hC 4
    have h5 : C 5 = 2 ∨ C 5 = 3 := by simpa [L] using hC 5
    have e03 := C.valid (show K33_P629.Adj 0 3 by decide)
    have e04 := C.valid (show K33_P629.Adj 0 4 by decide)
    have e05 := C.valid (show K33_P629.Adj 0 5 by decide)
    have e13 := C.valid (show K33_P629.Adj 1 3 by decide)
    have e14 := C.valid (show K33_P629.Adj 1 4 by decide)
    have e15 := C.valid (show K33_P629.Adj 1 5 by decide)
    have e23 := C.valid (show K33_P629.Adj 2 3 by decide)
    have e24 := C.valid (show K33_P629.Adj 2 4 by decide)
    have e25 := C.valid (show K33_P629.Adj 2 5 by decide)
    omega

theorem K33_lt_P629 : 2 < K33_P629.listChromaticNumber := by
  have hne : ({k | K33_P629.IsKChoosable k} : Set ℕ).Nonempty :=
    ⟨6, by simpa using isKChoosable_card_P629 K33_P629⟩
  refine Nat.lt_of_succ_le (le_csInf hne fun k hk => ?_)
  by_contra hlt
  exact K33_not_choosable_P629 k (by omega) hk

/-- Upper bound: `n 2 ≤ 6`, witnessed by `K_{3,3}`. -/
theorem n_two_le_six_P629 : n 2 ≤ 6 :=
  Nat.sInf_le ⟨K33_P629, K33_colorable_P629, K33_lt_P629⟩

/-- Colour one side `A` of a bipartite graph by `x` with all colours in `X`, and every other
vertex by a colour from its list outside `X`. -/
theorem exists_coloring_of_side_P629 {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (hA : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A)) (L : V → Finset ℕ) (X : Finset ℕ) (x : V → ℕ)
    (hx : ∀ a ∈ A, x a ∈ L a ∧ x a ∈ X) (hB : ∀ b ∉ A, ∃ y ∈ L b, y ∉ X) :
    ∃ C : G.Coloring ℕ, ∀ v, C v ∈ L v := by
  classical
  choose! y hyL hyX using hB
  refine ⟨Coloring.mk (fun v => if v ∈ A then x v else y v) fun {u v} huv heq => ?_, ?_⟩
  · have h := hA u v huv
    by_cases hu : u ∈ A
    · have hv : v ∉ A := h.1 hu
      simp only [hu, hv, if_true, if_false] at heq
      exact hyX v hv (heq ▸ (hx u hu).2)
    · have hv : v ∈ A := by tauto
      simp only [hu, hv, if_true, if_false] at heq
      exact hyX u hu (heq ▸ (hx v hv).2)
  · intro v
    by_cases hv : v ∈ A
    · show (if v ∈ A then x v else y v) ∈ L v
      rw [if_pos hv]
      exact (hx v hv).1
    · show (if v ∈ A then x v else y v) ∈ L v
      rw [if_neg hv]
      exact hyL v hv

/-- A two-element set inside two pairs forces the pairs to agree. -/
theorem pair_of_two_subsets_P629 (S : Finset ℕ) (hS : S.card = 2) (x y x' y' : ℕ)
    (h : S ⊆ {x, y}) (h' : S ⊆ {x', y'}) : (x = x' ∨ x = y') ∧ (y = x' ∨ y = y') := by
  obtain ⟨u, w, huw, rfl⟩ := Finset.card_eq_two.1 hS
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_insert,
    Finset.mem_singleton] at h h'
  omega

theorem not_subset_singleton_P629 (S : Finset ℕ) (hS : S.card = 2) (y : ℕ) : ¬ S ⊆ {y, y} := by
  intro h
  have := Finset.card_le_card h
  simp at this
  omega

/-- Two lists `P`, `Q` of size two and at most three further lists of size two: one can pick
`x₁ ∈ P`, `x₂ ∈ Q` such that none of the further lists is contained in `{x₁, x₂}`. -/
theorem exists_pair_P629 {V : Type*} (P Q : Finset ℕ) (hP : P.card = 2) (hQ : Q.card = 2)
    (B : Finset V) (hB : B.card ≤ 3) (L : V → Finset ℕ) (hL : ∀ v, (L v).card = 2) :
    ∃ x1 ∈ P, ∃ x2 ∈ Q, ∀ b ∈ B, ¬ L b ⊆ {x1, x2} := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 hP
  obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.1 hQ
  by_cases hcommon : p = r ∨ p = s ∨ q = r ∨ q = s
  · rcases hcommon with h | h | h | h
    · obtain ⟨b, -, hb⟩ := hcon p (by simp) p (by simp [h])
      exact not_subset_singleton_P629 _ (hL b) p hb
    · obtain ⟨b, -, hb⟩ := hcon p (by simp) p (by simp [h])
      exact not_subset_singleton_P629 _ (hL b) p hb
    · obtain ⟨b, -, hb⟩ := hcon q (by simp) q (by simp [h])
      exact not_subset_singleton_P629 _ (hL b) q hb
    · obtain ⟨b, -, hb⟩ := hcon q (by simp) q (by simp [h])
      exact not_subset_singleton_P629 _ (hL b) q hb
  · push Not at hcommon
    obtain ⟨hpr, hps, hqr, hqs⟩ := hcommon
    obtain ⟨b1, hb1, h1⟩ := hcon p (by simp) r (by simp)
    obtain ⟨b2, hb2, h2⟩ := hcon p (by simp) s (by simp)
    obtain ⟨b3, hb3, h3⟩ := hcon q (by simp) r (by simp)
    obtain ⟨b4, hb4, h4⟩ := hcon q (by simp) s (by simp)
    have d12 : b1 ≠ b2 := by
      rintro rfl
      have := pair_of_two_subsets_P629 _ (hL b1) _ _ _ _ h1 h2
      omega
    have d13 : b1 ≠ b3 := by
      rintro rfl
      have := pair_of_two_subsets_P629 _ (hL b1) _ _ _ _ h1 h3
      omega
    have d14 : b1 ≠ b4 := by
      rintro rfl
      have := pair_of_two_subsets_P629 _ (hL b1) _ _ _ _ h1 h4
      omega
    have d23 : b2 ≠ b3 := by
      rintro rfl
      have := pair_of_two_subsets_P629 _ (hL b2) _ _ _ _ h2 h3
      omega
    have d24 : b2 ≠ b4 := by
      rintro rfl
      have := pair_of_two_subsets_P629 _ (hL b2) _ _ _ _ h2 h4
      omega
    have d34 : b3 ≠ b4 := by
      rintro rfl
      have := pair_of_two_subsets_P629 _ (hL b3) _ _ _ _ h3 h4
      omega
    have hsub : ({b1, b2, b3, b4} : Finset V) ⊆ B := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> assumption
    have hcard : ({b1, b2, b3, b4} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [d12, d13, d14]),
        Finset.card_insert_of_notMem (by simp [d23, d24]), Finset.card_pair d34]
    have := Finset.card_le_card hsub
    omega

/-- A bipartite graph with a side `A` of size at most one, or of size two with at most three
vertices on the other side, is `2`-choosable. -/
theorem isKChoosable_two_of_side_P629 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (hA : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A))
    (h : A.card ≤ 1 ∨ (A.card = 2 ∧ Aᶜ.card ≤ 3)) : G.IsKChoosable 2 := by
  intro L hL
  rcases h with h | ⟨h2, hB⟩
  · have hne : ∀ v, (L v).Nonempty := fun v => Finset.card_pos.1 (by rw [hL v]; norm_num)
    choose x hx using hne
    refine exists_coloring_of_side_P629 G A hA L (A.image x) x
      (fun a ha => ⟨hx a, Finset.mem_image_of_mem x ha⟩) fun b _ => ?_
    by_contra hcon
    push Not at hcon
    have h1 := Finset.card_le_card (show L b ⊆ A.image x from hcon)
    have h2 := Finset.card_image_le (s := A) (f := x)
    rw [hL b] at h1
    omega
  · obtain ⟨a1, a2, hne, rfl⟩ := Finset.card_eq_two.1 h2
    obtain ⟨x1, hx1, x2, hx2, hgood⟩ :=
      exists_pair_P629 (L a1) (L a2) (hL a1) (hL a2) _ hB L hL
    refine exists_coloring_of_side_P629 G {a1, a2} hA L {x1, x2}
      (fun v => if v = a1 then x1 else x2) ?_ fun b hb => ?_
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp [hx1]
      · simp [hne.symm, hx2]
    · exact Finset.not_subset.1 (hgood b (Finset.mem_compl.2 hb))

/-- Lower bound core: every bipartite graph on at most five vertices is `2`-choosable. -/
theorem isKChoosable_two_of_colorable_P629 {m : ℕ} (hm : m ≤ 5) (G : SimpleGraph (Fin m))
    (hG : G.Colorable 2) : G.IsKChoosable 2 := by
  obtain ⟨c⟩ := hG
  let A : Finset (Fin m) := Finset.univ.filter (fun v => c v = 0)
  have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ↔ ¬ b = 0) := by decide
  have hA : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A) := by
    intro u v huv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact key _ _ (c.valid huv)
  have hAc : ∀ u v, G.Adj u v → (u ∈ Aᶜ ↔ v ∉ Aᶜ) := by
    intro u v huv
    simp only [Finset.mem_compl]
    have := hA u v huv
    tauto
  have hcard : A.card + Aᶜ.card = m := by rw [Finset.card_add_card_compl, Fintype.card_fin]
  by_cases h1 : A.card ≤ 2
  · exact isKChoosable_two_of_side_P629 G A hA (by omega)
  · exact isKChoosable_two_of_side_P629 G Aᶜ hAc (by rw [compl_compl]; omega)

/-- Lower bound: `6 ≤ n 2`. -/
theorem six_le_n_two_P629 : 6 ≤ n 2 := by
  have hne : {m : ℕ | ∃ G : SimpleGraph (Fin m), G.Colorable 2 ∧ 2 < G.listChromaticNumber}.Nonempty :=
    ⟨6, K33_P629, K33_colorable_P629, K33_lt_P629⟩
  unfold n
  refine le_csInf hne ?_
  rintro m ⟨G, hG, hlt⟩
  by_contra hm
  have h2 : G.listChromaticNumber ≤ 2 :=
    Nat.sInf_le (isKChoosable_two_of_colorable_P629 (by omega) G hG)
  omega

theorem erdos_629.variants.n_two : n 2 = 6 :=
  le_antisymm n_two_le_six_P629 six_le_n_two_P629

end OpenProofs.Erdos629
