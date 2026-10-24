import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-!
# `Arxiv.«0805.3777».isGenericRank_matrix`

Upstream: `Arxiv.«0805.3777».isGenericRank_matrix` (category textbook), `FormalConjectures/Arxiv/0805.3777/TensorRank.lean` line 181.
Proof idea: read a tensor `T : Holor ℂ [m, n]` as an `m × n` matrix. A rank-one holor
`x ⊗ y` gives a matrix `vecMulVec x y` of rank at most one and matrix rank is subadditive, so
matrix rank ≤ `cprank`. Conversely the row and column expansions `T = ∑ eᵢ ⊗ rowᵢ` and
`T = ∑ colⱼ ⊗ eⱼ` give `cprank T ≤ min m n` for every `T`. Take `U` to be the tensors whose
leading `k × k` minor (`k = min m n`) has nonzero determinant: it is open (determinant is
continuous), on it the matrix rank, hence `cprank`, is `k`, and it is dense because
`T + c • I` leaves `U` only at the finitely many roots `c` of a characteristic polynomial.
-/

open Arxiv.«0805.3777»

namespace OpenProofs.Arxiv.«0805.3777»

/-- The matrix of a 2-tensor. -/
def tensorRankMat {m n : ℕ} (T : Holor ℂ [m, n]) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => T ⟨[i.1, j.1], List.Forall₂.cons i.2 (List.Forall₂.cons j.2 List.Forall₂.nil)⟩

theorem tensorRankMat_ext {m n : ℕ} {T T' : Holor ℂ [m, n]}
    (h : tensorRankMat T = tensorRankMat T') : T = T' := by
  funext t
  obtain ⟨l, hl⟩ := t
  rcases hl with _ | ⟨hi, _ | ⟨hj, _ | _⟩⟩
  exact congrFun (congrFun h ⟨_, hi⟩) ⟨_, hj⟩

theorem tensorRankMat_mul {m n : ℕ} (x : Holor ℂ [m]) (y : Holor ℂ [n]) :
    tensorRankMat (Holor.mul x y : Holor ℂ [m, n]) =
      Matrix.vecMulVec (fun i : Fin m => x ⟨[i.1], List.Forall₂.cons i.2 List.Forall₂.nil⟩)
        (fun j : Fin n => y ⟨[j.1], List.Forall₂.cons j.2 List.Forall₂.nil⟩) := by
  ext i j
  rfl

theorem tensorRank_rank_add_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem tensorRank_rank_le_one {ds : List ℕ} {x : Holor ℂ ds} (hx : Holor.CPRankMax1 x) :
    ∀ (m n : ℕ) (_ : ds = [m, n]) (T : Holor ℂ [m, n]), HEq x T →
      (tensorRankMat T).rank ≤ 1 := by
  cases hx with
  | nil x => intro m n h; simp at h
  | cons x y _ =>
    intro m n h T hT
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl := (eq_of_heq hT).symm
    rw [tensorRankMat_mul]
    exact Matrix.rank_vecMulVec_le _ _

theorem tensorRank_rank_le {r : ℕ} {ds : List ℕ} {x : Holor ℂ ds} (hx : Holor.CPRankMax r x) :
    ∀ (m n : ℕ) (_ : ds = [m, n]) (T : Holor ℂ [m, n]), HEq x T →
      (tensorRankMat T).rank ≤ r := by
  induction hx with
  | zero =>
    intro m n h T hT
    subst h
    obtain rfl := (eq_of_heq hT).symm
    have : tensorRankMat (0 : Holor ℂ [m, n]) = 0 := rfl
    rw [this, Matrix.rank_zero]
  | succ k x y hx _ ih =>
    intro m n h T hT
    subst h
    obtain rfl := (eq_of_heq hT).symm
    have : tensorRankMat (x + y) = tensorRankMat x + tensorRankMat y := rfl
    rw [this]
    have h1 := tensorRank_rank_le_one hx m n rfl x HEq.rfl
    have h2 := ih m n rfl y HEq.rfl
    have := tensorRank_rank_add_le (tensorRankMat x) (tensorRankMat y)
    omega

theorem tensorRank_rank_le_cprank {m n : ℕ} (T : Holor ℂ [m, n]) :
    (tensorRankMat T).rank ≤ T.cprank := by
  have h : Holor.CPRankMax T.cprank T := by
    unfold Holor.cprank
    exact @Nat.find_spec (fun k => Holor.CPRankMax k T) (Classical.decPred _) _
  exact tensorRank_rank_le h m n rfl T HEq.rfl

theorem tensorRank_cprank_le {m n r : ℕ} (T : Holor ℂ [m, n]) (h : Holor.CPRankMax r T) :
    T.cprank ≤ r := by
  unfold Holor.cprank
  exact @Nat.find_min' _ (Classical.decPred _) _ _ h

/-- A vector as a 1-tensor. -/
def tensorRankVec {m : ℕ} (a : Fin m → ℂ) : Holor ℂ [m] := fun t =>
  if h : t.1.headI < m then a ⟨_, h⟩ else 0

/-- `tensorRankMat` as an additive map. -/
def tensorRankMatHom (m n : ℕ) : Holor ℂ [m, n] →+ Matrix (Fin m) (Fin n) ℂ where
  toFun := tensorRankMat
  map_zero' := rfl
  map_add' _ _ := rfl

theorem tensorRank_cprankMax_of_eq_sum {m n : ℕ} {ι : Type} (s : Finset ι)
    (a : ι → Fin m → ℂ) (b : ι → Fin n → ℂ) (T : Holor ℂ [m, n])
    (h : tensorRankMat T = ∑ k ∈ s, Matrix.vecMulVec (a k) (b k)) :
    Holor.CPRankMax s.card T := by
  let H : ι → Holor ℂ [m, n] := fun k =>
    Holor.mul (tensorRankVec (a k)) (Holor.mul (tensorRankVec (b k)) (fun _ => 1 : Holor ℂ []))
  have key : T = ∑ k ∈ s, H k := by
    apply tensorRankMat_ext
    have hs := map_sum (tensorRankMatHom m n) H s
    change tensorRankMat (∑ k ∈ s, H k) = ∑ k ∈ s, tensorRankMat (H k) at hs
    rw [h, hs]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext i j
    simp [H, tensorRankMat, Holor.mul, HolorIndex.take, HolorIndex.drop, tensorRankVec,
      Matrix.vecMulVec_apply]
  rw [key]
  simpa using Holor.cprankMax_sum s H fun k _ => Holor.cprankMax_1
    (Holor.CPRankMax1.cons _ _ (Holor.CPRankMax1.cons _ _ (Holor.CPRankMax1.nil _)))

theorem tensorRank_cprank_le_min {m n : ℕ} (T : Holor ℂ [m, n]) :
    T.cprank ≤ min m n := by
  classical
  apply le_min
  · have := tensorRank_cprankMax_of_eq_sum (Finset.univ : Finset (Fin m))
      (fun i => Pi.single i 1) (fun i j => tensorRankMat T i j) T (by
        ext i j
        simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply])
    simpa using tensorRank_cprank_le T this
  · have := tensorRank_cprankMax_of_eq_sum (Finset.univ : Finset (Fin n))
      (fun j i => tensorRankMat T i j) (fun j => Pi.single j 1) T (by
        ext i j
        simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply])
    simpa using tensorRank_cprank_le T this

theorem isGenericRank_matrix (m n : ℕ) : IsGenericRank [m, n] (min m n) := by
  classical
  set k := min m n with hk
  let A : Holor ℂ [m, n] → Matrix (Fin k) (Fin k) ℂ := fun T =>
    (tensorRankMat T).submatrix (Fin.castLE (min_le_left m n)) (Fin.castLE (min_le_right m n))
  have hMcont : Continuous (fun T : Holor ℂ [m, n] => tensorRankMat T) :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply _
  have hAcont : Continuous A := hMcont.matrix_submatrix _ _
  refine ⟨{T | (A T).det ≠ 0}, ?_, ?_, ?_⟩
  · exact isOpen_ne_fun hAcont.matrix_det continuous_const
  · rw [dense_iff_inter_open]
    rintro V hV ⟨T, hT⟩
    let E : Holor ℂ [m, n] := fun t => if t.1.headI = t.1.tail.headI then 1 else 0
    let f : ℂ → Holor ℂ [m, n] := fun c => T + c • E
    have hf : Continuous f := by
      show Continuous
        (fun c : ℂ => ((fun t => T t + c * E t : HolorIndex [m, n] → ℂ) : Holor ℂ [m, n]))
      exact continuous_pi fun t => continuous_const.add (continuous_id.mul continuous_const)
    have hAf : ∀ c : ℂ, A (f c) = Matrix.scalar (Fin k) c - (-A T) := by
      intro c
      ext i j
      change T _ + c * E _ = _
      simp [A, E, tensorRankMat, Matrix.scalar_apply, Matrix.diagonal_apply, Fin.ext_iff]
      split_ifs with h <;> simp [h, add_comm]
    have hp : Matrix.charpoly (-A T) ≠ 0 := (Matrix.charpoly_monic _).ne_zero
    have hZ : Dense {c : ℂ | ¬ (Matrix.charpoly (-A T)).IsRoot c} := by
      have := ((Polynomial.finite_setOfPred_isRoot hp).countable).dense_compl ℂ
      simpa [Set.compl_ofPred] using this
    obtain ⟨c, hcV, hc⟩ :=
      hZ.inter_open_nonempty (f ⁻¹' V) (hV.preimage hf) ⟨0, by simpa [f] using hT⟩
    refine ⟨f c, hcV, ?_⟩
    show (A (f c)).det ≠ 0
    rw [hAf, ← Matrix.eval_charpoly]
    exact hc
  · intro T hT
    apply le_antisymm (tensorRank_cprank_le_min T)
    refine le_trans ?_ (tensorRank_rank_le_cprank T)
    have hunit : IsUnit (A T) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hT)
    have := Matrix.rank_of_isUnit _ hunit
    simp only [Fintype.card_fin] at this
    rw [← hk, ← this]
    exact Matrix.rank_submatrix_le _ _ _

end OpenProofs.Arxiv.«0805.3777»
