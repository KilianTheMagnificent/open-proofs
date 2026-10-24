import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples

/-!
# `Arxiv.«1609.08688».maximalLength_four`

Upstream: `Arxiv.«1609.08688».maximalLength_four` (category test), `FormalConjectures/Arxiv/1609.08688/sIncreasingrTuples.lean` line 155.

Proof idea. Lower bound: the explicit `2`-increasing sequence
`(1,1,1), (1,2,2), (2,1,3), (2,2,4), (3,3,1), (3,4,2), (4,3,3), (4,4,4)` of length `8`.
Upper bound: encode a triple `a` with entries in `[1, 4]` as the number
`16 (a 0 - 1) + 4 (a 1 - 1) + (a 2 - 1) < 64`; the `2`-less relation becomes a boolean
relation `mlfLtCode` on codes. A depth-first search `mlfSearch k cands` (written with the
recursors directly, so that the kernel evaluates it cheaply) returns `true` whenever `cands`
contains a `mlfLtCode`-pairwise list of length at least `k`. The kernel checks, split into
chunks according to the first element of the list, that no such list of length `9` exists.
-/

open Arxiv.«1609.08688»

namespace OpenProofs.Arxiv.«1609.08688»

/-- The `2`-less relation on codes `16 x + 4 y + z` of triples `(x, y, z) ∈ [0, 4) ^ 3`. -/
def mlfLtCode (i j : ℕ) : Bool :=
  ((i / 16).blt (j / 16) && (i / 4 % 4).blt (j / 4 % 4)) ||
  ((i / 16).blt (j / 16) && (i % 4).blt (j % 4)) ||
  ((i / 4 % 4).blt (j / 4 % 4) && (i % 4).blt (j % 4))

/-- `List.filter`, written with the recursor (cheap for the kernel). -/
noncomputable def mlfFilter (p : ℕ → Bool) (l : List ℕ) : List ℕ :=
  List.rec [] (fun a _ ih => cond (p a) (a :: ih) ih) l

/-- `List.any`, written with the recursor (cheap for the kernel). -/
noncomputable def mlfAny (p : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec false (fun a _ ih => p a || ih) l

/-- `mlfSearch k cands` is `true` iff `cands` contains a chain of length `k`
for `mlfLtCode` (each element `mlfLtCode`-below all later ones). -/
noncomputable def mlfSearch (k : ℕ) : List ℕ → Bool :=
  Nat.rec (fun _ => true)
    (fun _ ih cands => mlfAny (fun b => ih (mlfFilter (mlfLtCode b) cands)) cands) k

theorem mlfFilter_mem {p : ℕ → Bool} {l : List ℕ} {x : ℕ} :
    x ∈ mlfFilter p l ↔ x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp [mlfFilter]
  | cons a l ih =>
    change x ∈ cond (p a) (a :: mlfFilter p l) (mlfFilter p l) ↔ _
    cases hpa : p a
    · simp only [cond_false, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · rw [hpa] at h2; exact absurd h2 (by simp)
        · exact ⟨h1, h2⟩
    · simp only [cond_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hpa⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩

theorem mlfAny_true_of_mem {p : ℕ → Bool} {l : List ℕ} {x : ℕ} (hx : x ∈ l)
    (hp : p x = true) : mlfAny p l = true := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    change (p a || mlfAny p l) = true
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [hp]
    · simp [ih hx]

theorem mlfAny_false_mem {p : ℕ → Bool} {l : List ℕ} {x : ℕ} (h : mlfAny p l = false)
    (hx : x ∈ l) : p x = false := by
  cases hpx : p x
  · rfl
  · rw [mlfAny_true_of_mem hx hpx] at h
    exact absurd h (by simp)

theorem mlfSearch_sound : ∀ (k : ℕ) (cands l : List ℕ),
    l.Pairwise (fun a b => mlfLtCode a b = true) → (∀ x ∈ l, x ∈ cands) →
    k ≤ l.length → mlfSearch k cands = true := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; rfl
  | succ k ih =>
    intro cands l hl hmem hlen
    cases l with
    | nil => simp at hlen
    | cons b l =>
      change mlfAny (fun b => mlfSearch k (mlfFilter (mlfLtCode b) cands)) cands = true
      refine mlfAny_true_of_mem (hmem b (by simp)) ?_
      rw [List.pairwise_cons] at hl
      refine ih _ l hl.2 (fun x hx => ?_) (by simpa using hlen)
      exact mlfFilter_mem.2 ⟨hmem x (by simp [hx]), hl.1 x hx⟩

theorem mlfChunk_0 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 0 1) = false := by decide +kernel

theorem mlfChunk_1 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 1 2) = false := by decide +kernel

theorem mlfChunk_3 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 3 3) = false := by decide +kernel

theorem mlfChunk_6 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 6 10) = false := by decide +kernel

theorem mlfChunk_16 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 16 4) = false := by decide +kernel

theorem mlfChunk_20 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 20 28) = false := by decide +kernel

theorem mlfChunk_48 :
    mlfAny (fun b => mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)))
      (List.range' 48 16) = false := by decide +kernel

theorem mlfSearch_eight_false {b : ℕ} (hb : b < 64) :
    mlfSearch 8 (mlfFilter (mlfLtCode b) (List.range 64)) = false := by
  by_cases h1 : b < 1
  · exact mlfAny_false_mem mlfChunk_0 (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h3 : b < 3
  · exact mlfAny_false_mem mlfChunk_1 (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h6 : b < 6
  · exact mlfAny_false_mem mlfChunk_3 (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h16 : b < 16
  · exact mlfAny_false_mem mlfChunk_6 (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h20 : b < 20
  · exact mlfAny_false_mem mlfChunk_16 (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h48 : b < 48
  · exact mlfAny_false_mem mlfChunk_20 (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact mlfAny_false_mem mlfChunk_48 (List.mem_range'_1.2 ⟨by omega, by omega⟩)

/-- Code of a triple with entries in `[1, 4]`. -/
def mlfEnc (a : Fin 3 → ℕ) : ℕ := 16 * (a 0 - 1) + 4 * (a 1 - 1) + (a 2 - 1)

theorem mlfEnc_spec {a : Fin 3 → ℕ} (h : Set.range a ⊆ Set.Icc 1 4) :
    mlfEnc a / 16 = a 0 - 1 ∧ mlfEnc a / 4 % 4 = a 1 - 1 ∧ mlfEnc a % 4 = a 2 - 1 ∧
      mlfEnc a < 64 := by
  have h0 := h ⟨0, rfl⟩
  have h1 := h ⟨1, rfl⟩
  have h2 := h ⟨2, rfl⟩
  simp only [Set.mem_Icc] at h0 h1 h2
  unfold mlfEnc
  omega

theorem mlfLtCode_of_lt₂ {a b : Fin 3 → ℕ} (ha : Set.range a ⊆ Set.Icc 1 4)
    (hb : Set.range b ⊆ Set.Icc 1 4) (h : lt₂ a b) :
    mlfLtCode (mlfEnc a) (mlfEnc b) = true := by
  obtain ⟨ea0, ea1, ea2, -⟩ := mlfEnc_spec ha
  obtain ⟨eb0, eb1, eb2, -⟩ := mlfEnc_spec hb
  have ha0 := ha ⟨0, rfl⟩
  have ha1 := ha ⟨1, rfl⟩
  have ha2 := ha ⟨2, rfl⟩
  have hb0 := hb ⟨0, rfl⟩
  have hb1 := hb ⟨1, rfl⟩
  have hb2 := hb ⟨2, rfl⟩
  simp only [Set.mem_Icc] at ha0 ha1 ha2 hb0 hb1 hb2
  unfold mlfLtCode
  rw [ea0, ea1, ea2, eb0, eb1, eb2]
  obtain ⟨i, j, hij, hi, hj⟩ := h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq]
  fin_cases i <;> fin_cases j <;> simp at hij hi hj ⊢ <;> omega

theorem mlfLength_le {s : List (Fin 3 → ℕ)} (hs : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 4)
    (hinc : IsIncreasing₂ s) : s.length ≤ 8 := by
  by_contra hlen
  have hpw : (s.map mlfEnc).Pairwise (fun a b => mlfLtCode a b = true) := by
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem
      (fun {a b} ha hb hab => mlfLtCode_of_lt₂ (hs a ha) (hs b hb) hab) hinc
  have hlt : ∀ x ∈ s.map mlfEnc, x < 64 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact (mlfEnc_spec (hs a ha)).2.2.2
  have hlen' : 9 ≤ (s.map mlfEnc).length := by rw [List.length_map]; omega
  generalize s.map mlfEnc = l at hpw hlt hlen'
  cases l with
  | nil => simp at hlen'
  | cons b l =>
    rw [List.pairwise_cons] at hpw
    have hb : b < 64 := hlt b (by simp)
    have := mlfSearch_sound 8 (mlfFilter (mlfLtCode b) (List.range 64)) l hpw.2
      (fun x hx => mlfFilter_mem.2 ⟨List.mem_range.2 (hlt x (by simp [hx])), hpw.1 x hx⟩)
      (by simpa using hlen')
    rw [mlfSearch_eight_false hb] at this
    exact absurd this (by simp)

theorem maximalLength_four : maximalLength 4 = 8 := by
  unfold maximalLength
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · refine ⟨[![1, 1, 1], ![1, 2, 2], ![2, 1, 3], ![2, 2, 4], ![3, 3, 1], ![3, 4, 2],
      ![4, 3, 3], ![4, 4, 4]], ?_, ?_, rfl⟩
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rintro _ ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        fin_cases i <;> simp
    · unfold IsIncreasing₂ lt₂
      decide
  · rintro _ ⟨s, hs, hinc, rfl⟩
    exact mlfLength_le hs hinc

end OpenProofs.Arxiv.«1609.08688»
