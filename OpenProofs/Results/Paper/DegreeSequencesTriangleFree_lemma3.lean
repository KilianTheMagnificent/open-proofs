import FormalConjectures.Paper.DegreeSequencesTriangleFree

/-!
# `SimpleGraph.lemma3`

Upstream: `SimpleGraph.lemma3` (category API), `FormalConjectures/Paper/DegreeSequencesTriangleFree.lean` line 262.

Proof idea: an explicit interval bigraph. Vertices `i < 5n` form one side, vertices
`5n ≤ v < 8n` the other, and `i ~ v` iff `2i + 1 ≤ v + 3n` and `v ≤ i / 2 + 6n`. Every
neighbourhood is an interval, so the degrees have closed forms (`efsL3Deg`): the vertices
`i < 4n` have degree `i / 2 + n + 1`, the vertices `4n ≤ i < 5n` have degree `11n - 1 - 2i`,
and the other side has degrees `≥ 3n` or of the parity of `n`. The degree together with a
code in `{0, 1, 2}` (`efsL3Code`) determines the vertex, so no degree occurs more than three
times, while `n + 1` occurs exactly three times (vertices `0`, `1`, `5n - 1`) and is the
minimum degree.
-/

open BigOperators
open scoped Finset
open SimpleGraph

namespace OpenProofs.SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (d : ℕ → ℕ) (n k r : ℕ)
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The adjacency relation of the construction, on vertex labels. -/
def efsL3Rel (n u v : ℕ) : Prop :=
  u < 5 * n ∧ 5 * n ≤ v ∧ 2 * u + 1 ≤ v + 3 * n ∧ v ≤ u / 2 + 6 * n

instance (n u v : ℕ) : Decidable (efsL3Rel n u v) := by
  unfold efsL3Rel; infer_instance

/-- The graph of the construction on `Fin (8 * n)`. -/
def efsL3Graph (n : ℕ) : _root_.SimpleGraph (Fin (8 * n)) where
  Adj u v := efsL3Rel n u v ∨ efsL3Rel n v u
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by unfold efsL3Rel at h; omega⟩

instance efsL3Graph_decRel (n : ℕ) : DecidableRel (efsL3Graph n).Adj := fun u v =>
  inferInstanceAs (Decidable (efsL3Rel n u v ∨ efsL3Rel n v u))

/-- Closed form of the degrees. -/
def efsL3Deg (n v : ℕ) : ℕ :=
  if v < 5 * n then min (3 * n) (v / 2 + n + 1) - (2 * v + 1 - 8 * n)
  else min (5 * n) ((v + 3 * n + 1) / 2) - 2 * (v - 6 * n)

/-- A code that separates vertices of equal degree. -/
def efsL3Code (n v : ℕ) : ℕ :=
  if v < 4 * n then v % 2 else if v < 5 * n then 2 else if v < 6 * n then (v + 1) % 2 else 2

lemma efsL3_degree (n : ℕ) (v : Fin (8 * n)) :
    (efsL3Graph n).degree v = efsL3Deg n v := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter,
    ← Finset.card_map Fin.valEmbedding]
  have hv8 := v.isLt
  by_cases hv : (v : ℕ) < 5 * n
  · have : ({w | (efsL3Graph n).Adj v w} : Finset (Fin (8 * n))).map Fin.valEmbedding =
        Finset.Ico (5 * n + (2 * v + 1 - 8 * n)) (5 * n + min (3 * n) (v / 2 + n + 1)) := by
      ext k
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have := w.isLt
        change efsL3Rel n v w ∨ efsL3Rel n w v at hw
        unfold efsL3Rel at hw
        omega
      · intro hk
        refine ⟨⟨k, by omega⟩, ?_, rfl⟩
        change efsL3Rel n v k ∨ efsL3Rel n k v
        unfold efsL3Rel
        omega
    rw [this, Nat.card_Ico]
    unfold efsL3Deg
    rw [if_pos hv]
    omega
  · have : ({w | (efsL3Graph n).Adj v w} : Finset (Fin (8 * n))).map Fin.valEmbedding =
        Finset.Ico (2 * (v - 6 * n)) (min (5 * n) ((v + 3 * n + 1) / 2)) := by
      ext k
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have := w.isLt
        change efsL3Rel n v w ∨ efsL3Rel n w v at hw
        unfold efsL3Rel at hw
        omega
      · intro hk
        refine ⟨⟨k, by omega⟩, ?_, rfl⟩
        change efsL3Rel n v k ∨ efsL3Rel n k v
        unfold efsL3Rel
        omega
    rw [this, Nat.card_Ico]
    unfold efsL3Deg
    rw [if_neg hv]

lemma efsL3_deg_ge (n v : ℕ) (hv : v < 8 * n) : n + 1 ≤ efsL3Deg n v := by
  unfold efsL3Deg
  split_ifs <;> omega

lemma efsL3_code_lt (n v : ℕ) : efsL3Code n v < 3 := by
  unfold efsL3Code
  split_ifs <;> omega

lemma efsL3_inj (n u v : ℕ) (hu : u < 8 * n) (hv : v < 8 * n)
    (hd : efsL3Deg n u = efsL3Deg n v) (hc : efsL3Code n u = efsL3Code n v) : u = v := by
  unfold efsL3Deg at hd
  unfold efsL3Code at hc
  split_ifs at hd hc <;> omega

lemma efsL3_count_le (n d : ℕ) :
    #({v | (efsL3Graph n).degree v = d} : Finset (Fin (8 * n))) ≤ 3 := by
  calc #({v | (efsL3Graph n).degree v = d} : Finset (Fin (8 * n)))
      ≤ #(Finset.range 3) := by
        apply Finset.card_le_card_of_injOn (fun v : Fin (8 * n) => efsL3Code n v)
        · intro v _
          simpa using efsL3_code_lt n v
        · intro u hu v hv huv
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
          rw [efsL3_degree] at hu hv
          exact Fin.ext (efsL3_inj n u v u.isLt v.isLt (hu.trans hv.symm) huv)
    _ = 3 := Finset.card_range 3

lemma efsL3_count_eq (n : ℕ) (hn : 0 < n) :
    #({v | (efsL3Graph n).degree v = n + 1} : Finset (Fin (8 * n))) = 3 := by
  apply le_antisymm (efsL3_count_le n (n + 1))
  have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨5 * n - 1, by omega⟩} : Finset (Fin (8 * n))) ⊆
      ({v | (efsL3Graph n).degree v = n + 1} : Finset (Fin (8 * n))) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, efsL3_degree]
    unfold efsL3Deg
    rcases hv with rfl | rfl | rfl <;> simp only [] <;> split_ifs <;> omega
  refine le_trans ?_ (Finset.card_le_card hsub)
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton, Fin.ext_iff]; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega

lemma efsL3_listCount (n d : ℕ) :
    (degreeSequence (efsL3Graph n)).count d =
      #({v | (efsL3Graph n).degree v = d} : Finset (Fin (8 * n))) := by
  have hco : (↑(degreeSequence (efsL3Graph n)) : Multiset ℕ) =
      Finset.univ.val.map (fun v : Fin (8 * n) => (efsL3Graph n).degree v) := by
    unfold degreeSequence
    exact Multiset.sort_eq _ _
  rw [← Multiset.coe_count, hco, Multiset.count_map]
  simp only [← Finset.filter_val, Finset.card_val, eq_comm]

theorem lemma3 (n : ℕ) (hn : 0 < n) :
    ∃ (G : SimpleGraph (Fin (8 * n))) (_ : DecidableRel G.Adj),
      G.IsBipartite ∧ G.minDegree = n + 1 ∧ degreeSequenceMultiplicity G = 3 := by
  refine ⟨efsL3Graph n, inferInstance, ?_, ?_, ?_⟩
  · refine IsBipartiteWith.isBipartite (s := {v | (v : ℕ) < 5 * n}) (t := {v | 5 * n ≤ (v : ℕ)})
      ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hv hv'
      simp only [Set.mem_ofPred_eq] at hv hv'
      omega
    · intro v w h
      change efsL3Rel n v w ∨ efsL3Rel n w v at h
      unfold efsL3Rel at h
      simp only [Set.mem_ofPred_eq]
      omega
  · have : Nonempty (Fin (8 * n)) := ⟨⟨0, by omega⟩⟩
    apply le_antisymm
    · refine (minDegree_le_degree _ (⟨0, by omega⟩ : Fin (8 * n))).trans_eq ?_
      rw [efsL3_degree]
      unfold efsL3Deg
      simp only []
      split_ifs <;> omega
    · apply le_minDegree_of_forall_le_degree
      intro v
      rw [efsL3_degree]
      exact efsL3_deg_ge n v v.isLt
  · unfold degreeSequenceMultiplicity
    have hmax : ((degreeSequence (efsL3Graph n)).map
        (fun d => (degreeSequence (efsL3Graph n)).count d)).max? = some 3 := by
      rw [List.max?_eq_some_iff]
      constructor
      · rw [List.mem_map]
        refine ⟨n + 1, ?_, ?_⟩
        · rw [← List.count_pos_iff, efsL3_listCount, efsL3_count_eq n hn]
          omega
        · rw [efsL3_listCount, efsL3_count_eq n hn]
      · intro b hb
        rw [List.mem_map] at hb
        obtain ⟨d, -, rfl⟩ := hb
        rw [efsL3_listCount]
        exact efsL3_count_le n d
    simp only [hmax, Option.getD_some]

end OpenProofs.SimpleGraph
