import FormalConjectures.Paper.WeaklyFirstCountable

/-!
# `WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable`

Upstream: `WeaklyFirstCountable.exists_weakly_first_countable_not_first_countable` (category textbook), `FormalConjectures/Paper/WeaklyFirstCountable.lean` line 73.
Proof idea: the Arens space on `Option (ℕ × Option ℕ)`: `none` is the apex, `some (i, none)` the
`i`-th limit point and `some (i, some j)` the isolated points. We give the weak base
`V none n = {none} ∪ {some (i, none) | n ≤ i}`, `V (some (i, none)) n = {some (i, none)} ∪
{some (i, some j) | n ≤ j}`, `V b n = {b}` and take as open sets exactly those `O` with
`∀ x ∈ O, ∃ k, V x k ⊆ O` (a topology because each `V x` is antitone), so the space is weakly
first countable by definition. It is not first countable: the apex lies in the closure of the
isolated points, but no sequence of isolated points `some (i n, some (j n))` converges to it.
Indeed the first coordinates `i n` would have to tend to infinity (open sets
`{x | first coordinate ≥ N}`), and then the open set of points `some (a, some b)` with
`b > f a`, `f a = ∑_{n < M a} j n` (where `i n > a` for `n ≥ M a`), contains no term of the
sequence.
-/

open TopologicalSpace Topology Filter
open scoped Cardinal
open WeaklyFirstCountable

namespace OpenProofs.WeaklyFirstCountable

/-- Weak base of the Arens space on `Option (ℕ × Option ℕ)`: `none` is the apex,
`some (i, none)` the `i`-th limit point, `some (i, some j)` the isolated points. -/
def arensWeakBase : Option (ℕ × Option ℕ) → ℕ → Set (Option (ℕ × Option ℕ))
  | none, n => {x | x = none ∨ ∃ i, n ≤ i ∧ x = some (i, none)}
  | some (i, none), n => {x | x = some (i, none) ∨ ∃ j, n ≤ j ∧ x = some (i, some j)}
  | some (i, some j), _ => {some (i, some j)}

theorem arensWeakBase_antitone (x : Option (ℕ × Option ℕ)) : Antitone (arensWeakBase x) := by
  intro m n hmn y hy
  rcases x with _ | ⟨i, _ | j⟩
  · simp only [arensWeakBase, Set.mem_ofPred_eq] at hy ⊢
    rcases hy with h | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hmn.trans hi, h⟩
  · simp only [arensWeakBase, Set.mem_ofPred_eq] at hy ⊢
    rcases hy with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hmn.trans hj, h⟩
  · exact hy

theorem self_mem_arensWeakBase (x : Option (ℕ × Option ℕ)) (n : ℕ) :
    x ∈ arensWeakBase x n := by
  rcases x with _ | ⟨i, _ | j⟩ <;> simp [arensWeakBase]

/-- The topology whose open sets are the sets containing some `arensWeakBase x k` around each
of their points. -/
def arensTopology : TopologicalSpace (Option (ℕ × Option ℕ)) where
  IsOpen O := ∀ x ∈ O, ∃ k, arensWeakBase x k ⊆ O
  isOpen_univ x _ := ⟨0, Set.subset_univ _⟩
  isOpen_inter s t hs ht x hx := by
    obtain ⟨a, ha⟩ := hs x hx.1
    obtain ⟨b, hb⟩ := ht x hx.2
    exact ⟨max a b, fun y hy =>
      ⟨ha (arensWeakBase_antitone x (le_max_left a b) hy),
        hb (arensWeakBase_antitone x (le_max_right a b) hy)⟩⟩
  isOpen_sUnion S hS x hx := by
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨k, hk⟩ := hS t ht x hxt
    exact ⟨k, hk.trans (Set.subset_sUnion_of_mem ht)⟩

theorem exists_weakly_first_countable_not_first_countable : ∃ (X : Type) (_ : TopologicalSpace X),
      WeaklyFirstCountableTopology X ∧ ¬ FirstCountableTopology X := by
  let _ : TopologicalSpace (Option (ℕ × Option ℕ)) := arensTopology
  refine ⟨Option (ℕ × Option ℕ), arensTopology, ⟨⟨arensWeakBase,
    fun x => ⟨arensWeakBase_antitone x, self_mem_arensWeakBase x⟩, fun O => Iff.rfl⟩⟩, ?_⟩
  intro hfc
  have hcl : (none : Option (ℕ × Option ℕ)) ∈
      closure {x : Option (ℕ × Option ℕ) | ∃ i j, x = some (i, some j)} := by
    rw [mem_closure_iff]
    intro o ho hno
    obtain ⟨k, hk⟩ := ho none hno
    have h1 : some (k, none) ∈ o := hk (Or.inr ⟨k, le_rfl, rfl⟩)
    obtain ⟨k', hk'⟩ := ho _ h1
    exact ⟨some (k, some k'), hk' (Or.inr ⟨k', le_rfl, rfl⟩), k, k', rfl⟩
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose i j hij using hs
  -- the first coordinates tend to infinity
  have hi : ∀ N, ∀ᶠ n in atTop, N ≤ i n := by
    intro N
    have hO : IsOpen {x : Option (ℕ × Option ℕ) | ∀ p, x = some p → N ≤ p.1} := by
      intro x hx
      rcases x with _ | ⟨a, _ | b⟩
      · refine ⟨N, ?_⟩
        rintro y (rfl | ⟨a', ha', rfl⟩)
        · intro p hp
          cases hp
        · intro p hp
          cases hp
          exact ha'
      · refine ⟨0, ?_⟩
        rintro y (rfl | ⟨b', -, rfl⟩)
        · exact hx
        · intro p hp
          cases hp
          exact hx (a, none) rfl
      · exact ⟨0, fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hx⟩
    exact Filter.Eventually.mono (hlim (hO.mem_nhds (fun p hp => by cases hp)))
      fun n hn => hn (i n, some (j n)) (hij n)
  have hM : ∀ a, ∃ M, ∀ n, M ≤ n → a + 1 ≤ i n := fun a => eventually_atTop.mp (hi (a + 1))
  choose M hM using hM
  have hjf : ∀ n, j n ≤ ∑ m ∈ Finset.range (M (i n)), j m := by
    intro n
    have hn : n < M (i n) := by
      by_contra h
      have := hM (i n) n (not_lt.mp h)
      omega
    exact Finset.single_le_sum (f := j) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
  have hO : IsOpen {x : Option (ℕ × Option ℕ) |
      ∀ a b, x = some (a, some b) → ∑ m ∈ Finset.range (M a), j m < b} := by
    intro x hx
    rcases x with _ | ⟨a, _ | b⟩
    · refine ⟨0, ?_⟩
      rintro y (rfl | ⟨a', -, rfl⟩)
      · intro a b h
        cases h
      · intro a b h
        cases h
    · refine ⟨∑ m ∈ Finset.range (M a), j m + 1, ?_⟩
      rintro y (rfl | ⟨b', hb', rfl⟩)
      · intro a b h
        cases h
      · intro a' b h
        cases h
        omega
    · exact ⟨0, fun y hy => by rw [Set.mem_singleton_iff.mp hy]; exact hx⟩
  have hev := hlim (hO.mem_nhds (fun a b h => by cases h))
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (f := atTop) hev
  have h1 := hn (i n) (j n) (hij n)
  have h2 := hjf n
  omega

end OpenProofs.WeaklyFirstCountable
