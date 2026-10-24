import FormalConjectures.ErdosProblems.«1088»

/-!
# `Erdos1088.f_isLeast`

Upstream: `Erdos1088.f_isLeast` (category API), `FormalConjectures/ErdosProblems/1088.lean` line 58.
Proof idea: `IsLeast s (sInf s)` on `ℕ` only needs `s` nonempty, i.e. `f_d(n)` is finite: every
large enough finite set in `ℝ^d` contains `n` points with all pairwise distances distinct.
Induction on the dimension `k` of the affine span. Take a maximal distinct-distance subset `A`
of `S` (size `< n`, else done). Every other point of `S` lies on a bisector hyperplane of two
points of `A` or on a sphere centred at a point of `A` whose radius is a distance of `A`; by
pigeonhole one of these `≤ 2 n³` sets holds many points of `S`. A bisector, and a sphere
intersected with a sphere containing `S`, lie in a hyperplane missing a point of `S`, so the
affine dimension drops. A sphere alone is handled by a separate statement for sets on a sphere.
-/

open Filter
open scoped EuclideanGeometry
open Erdos1088

namespace OpenProofs.Erdos1088

variable {d : ℕ}

/-- All pairwise distances distinct, as an injectivity statement. -/
def DistInj (A : Finset (ℝ^d)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → dist a b = dist c e →
    (a = c ∧ b = e) ∨ (a = e ∧ b = c)

/-- Dimension of the affine span of a finite set. -/
noncomputable def affRank (S : Finset (ℝ^d)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (S : Set (ℝ^d)))

/-- `S` contains an `n`-point subset with all distances distinct. -/
def GoodSet (n : ℕ) (S : Finset (ℝ^d)) : Prop :=
  ∃ A ⊆ S, A.card = n ∧ DistInj A

lemma distInj_mono {A B : Finset (ℝ^d)} (hA : DistInj A) (hBA : B ⊆ A) : DistInj B :=
  fun a ha b hb c hc e he => hA a (hBA ha) b (hBA hb) c (hBA hc) e (hBA he)

lemma goodSet_mono {n : ℕ} {T S : Finset (ℝ^d)} (hT : GoodSet n T) (hTS : T ⊆ S) :
    GoodSet n S := by
  obtain ⟨A, hAT, hA, hD⟩ := hT
  exact ⟨A, hAT.trans hTS, hA, hD⟩

lemma pairwise_of_distInj {A : Finset (ℝ^d)} (hA : DistInj A) : PairwiseDistancesDistinct A := by
  unfold PairwiseDistancesDistinct distinctDistances distanceSet
  rw [← Sym2.card_image_offDiag]
  have h1 : A.offDiag.image (fun pair : ℝ^d × ℝ^d => dist pair.1 pair.2) =
      (A.offDiag.image Sym2.mk.uncurry).image
        (Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩) := by
    rw [Finset.image_image]
    rfl
  rw [h1]
  apply Finset.card_image_of_injOn
  intro z1 hz1 z2 hz2 heq
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz1
  obtain ⟨⟨c, e⟩, hce, rfl⟩ := Finset.mem_image.mp hz2
  rw [Finset.mem_offDiag] at hab hce
  have hd : dist a b = dist c e := heq
  rcases hA a hab.1 b hab.2.1 c hce.1 e hce.2.1 hab.2.2 hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

lemma affRank_lt {T S : Finset (ℝ^d)} (hTS : T ⊆ S) (a b : ℝ^d) (κ : ℝ)
    (hT : ∀ p ∈ T, dist p a ^ 2 - dist p b ^ 2 = κ) {x : ℝ^d} (hx : x ∈ S)
    (hxk : dist x a ^ 2 - dist x b ^ 2 ≠ κ) (hne : T.Nonempty) : affRank T < affRank S := by
  have key : ∀ p q : ℝ^d, (dist p a ^ 2 - dist p b ^ 2) - (dist q a ^ 2 - dist q b ^ 2)
      = 2 * inner ℝ (p - q) (b - a) := by
    intro p q
    simp only [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      real_inner_comm]
    ring
  obtain ⟨t0, ht0⟩ := hne
  have hle : vectorSpan ℝ (T : Set (ℝ^d)) ≤ (ℝ ∙ (b - a))ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    show inner ℝ (b - a) (p - q) = 0
    rw [real_inner_comm]
    have := key p q
    rw [hT p hp, hT q hq, sub_self] at this
    linarith
  have hlt : vectorSpan ℝ (T : Set (ℝ^d)) < vectorSpan ℝ (S : Set (ℝ^d)) := by
    refine lt_of_le_of_ne (vectorSpan_mono ℝ (Finset.coe_subset.mpr hTS)) ?_
    intro heq
    have hmem : x -ᵥ t0 ∈ vectorSpan ℝ (T : Set (ℝ^d)) := by
      rw [heq]
      exact vsub_mem_vectorSpan ℝ (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr (hTS ht0))
    have h2 := hle hmem
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub, real_inner_comm] at h2
    have h3 := key x t0
    rw [hT t0 ht0, h2] at h3
    exact hxk (by linarith)
  exact Submodule.finrank_lt_finrank_of_lt hlt

lemma affRank_mono {T S : Finset (ℝ^d)} (hTS : T ⊆ S) : affRank T ≤ affRank S :=
  Submodule.finrank_mono (vectorSpan_mono ℝ (Finset.coe_subset.mpr hTS))

lemma affRank_lt_succ (S : Finset (ℝ^d)) : affRank S < d + 1 :=
  Nat.lt_succ_of_le ((Submodule.finrank_le _).trans finrank_euclideanSpace_fin.le)

lemma cover (S : Finset (ℝ^d)) (n : ℕ) (hS : ¬ GoodSet n S) :
    ∃ A ⊆ S, A.card < n ∧ ∀ p ∈ S, p ∈ A ∨
      (∃ i ∈ A ×ˢ A ×ˢ A, i.1 ≠ i.2.1 ∧ dist p i.1 = dist p i.2.1) ∨
      (∃ i ∈ A ×ˢ A ×ˢ A, i.2.1 ≠ i.2.2 ∧ dist p i.1 = dist i.2.1 i.2.2) := by
  classical
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image (S.powerset.filter DistInj) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset S, by simp [DistInj]⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  have hAn : A.card < n := by
    by_contra h
    push Not at h
    obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq h
    exact hS ⟨B, hBA.trans hA.1, hB, distInj_mono hA.2 hBA⟩
  refine ⟨A, hA.1, hAn, fun p hp => ?_⟩
  by_cases hpA : p ∈ A
  · exact Or.inl hpA
  have bis : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist p x = dist p y →
      p ∈ A ∨ (∃ i ∈ A ×ˢ A ×ˢ A, i.1 ≠ i.2.1 ∧ dist p i.1 = dist p i.2.1) ∨
      (∃ i ∈ A ×ˢ A ×ˢ A, i.2.1 ≠ i.2.2 ∧ dist p i.1 = dist i.2.1 i.2.2) :=
    fun x hx y hy hxy h =>
      Or.inr (Or.inl ⟨(x, y, x), by simp [Finset.mem_product, hx, hy], hxy, h⟩)
  have sph : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, y ≠ z → dist p x = dist y z →
      p ∈ A ∨ (∃ i ∈ A ×ˢ A ×ˢ A, i.1 ≠ i.2.1 ∧ dist p i.1 = dist p i.2.1) ∨
      (∃ i ∈ A ×ˢ A ×ˢ A, i.2.1 ≠ i.2.2 ∧ dist p i.1 = dist i.2.1 i.2.2) :=
    fun x hx y hy z hz hyz h =>
      Or.inr (Or.inr ⟨(x, y, z), by simp [Finset.mem_product, hx, hy, hz], hyz, h⟩)
  have hnot : ¬ DistInj (insert p A) := by
    intro h
    have := hmax (insert p A) (by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset hp hA.1, h⟩)
    rw [Finset.card_insert_of_notMem hpA] at this
    omega
  unfold DistInj at hnot
  push Not at hnot
  obtain ⟨a, ha, b, hb, c, hc, e, he, hab, hd, h1, h2⟩ := hnot
  rw [Finset.mem_insert] at ha hb hc he
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rcases he with he | he
  all_goals (try subst a)
  all_goals (try subst b)
  all_goals (try subst c)
  all_goals (try subst e)
  · exact absurd rfl hab
  · exact absurd rfl hab
  · exact absurd rfl hab
  · exact absurd rfl hab
  · exact absurd (dist_eq_zero.mp (hd.trans (dist_self p))) hab
  · exact bis b hb e he (h1 rfl) hd
  · exact bis b hb c hc (h2 rfl) (hd.trans (dist_comm c p))
  · exact sph b hb c hc e he
      (fun hce => hab (dist_eq_zero.mp (hd.trans (by rw [hce, dist_self])))) hd
  · exact absurd (dist_eq_zero.mp (hd.trans (dist_self p))) hab
  · exact bis a ha e he (fun hae => h2 hae rfl) ((dist_comm p a).trans hd)
  · exact bis a ha c hc (fun h => h1 h rfl) (by rw [dist_comm p a, dist_comm p c]; exact hd)
  · exact sph a ha c hc e he
      (fun hce => hab (dist_eq_zero.mp (hd.trans (by rw [hce, dist_self]))))
      ((dist_comm p a).trans hd)
  · exact absurd (dist_eq_zero.mp (hd.trans (dist_self p))) hab
  · exact sph e he a ha b hb hab hd.symm
  · exact sph c hc a ha b hb hab ((dist_comm p c).trans hd.symm)
  · rcases hA.2 a ha b hb c hc e he hab hd with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact absurd h4 (h1 h3)
    · exact absurd h4 (h2 h3)

lemma core (S : Finset (ℝ^d)) (n M : ℕ) (hG : ¬ GoodSet n S)
    (hcard : n + 2 * n ^ 3 * M < S.card) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S,
      M < (S.filter (fun p => x ≠ y ∧ dist p x = dist p y)).card ∨
      M < (S.filter (fun p => y ≠ z ∧ dist p x = dist y z)).card := by
  classical
  obtain ⟨A, hAS, hAn, hcov⟩ := cover S n hG
  by_contra h
  push Not at h
  set I := A ×ˢ A ×ˢ A with hI
  set F1 : ℝ^d × ℝ^d × ℝ^d → Finset (ℝ^d) :=
    fun i => S.filter (fun p => i.1 ≠ i.2.1 ∧ dist p i.1 = dist p i.2.1) with hF1
  set F2 : ℝ^d × ℝ^d × ℝ^d → Finset (ℝ^d) :=
    fun i => S.filter (fun p => i.2.1 ≠ i.2.2 ∧ dist p i.1 = dist i.2.1 i.2.2) with hF2
  have hmemI : ∀ i ∈ I, i.1 ∈ S ∧ i.2.1 ∈ S ∧ i.2.2 ∈ S := by
    intro i hi
    simp only [hI, Finset.mem_product] at hi
    exact ⟨hAS hi.1, hAS hi.2.1, hAS hi.2.2⟩
  have hsub : S ⊆ A ∪ (I.biUnion F1 ∪ I.biUnion F2) := by
    intro p hp
    rcases hcov p hp with h0 | ⟨i, hi, hP⟩ | ⟨i, hi, hQ⟩
    · exact Finset.mem_union_left _ h0
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hp, hP⟩⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hp, hQ⟩⟩))
  have hc1 : S.card ≤ A.card + (∑ i ∈ I, (F1 i).card + ∑ i ∈ I, (F2 i).card) :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left ((Finset.card_union_le _ _).trans
        (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le)) _))
  have hs1 : ∑ i ∈ I, (F1 i).card ≤ I.card * M := by
    have := Finset.sum_le_card_nsmul I (fun i => (F1 i).card) M (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hmemI i hi
      exact (h i.1 h1 i.2.1 h2 i.2.2 h3).1)
    simpa using this
  have hs2 : ∑ i ∈ I, (F2 i).card ≤ I.card * M := by
    have := Finset.sum_le_card_nsmul I (fun i => (F2 i).card) M (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := hmemI i hi
      exact (h i.1 h1 i.2.1 h2 i.2.2 h3).2)
    simpa using this
  have hIc : I.card ≤ n ^ 3 := by
    rw [hI, Finset.card_product, Finset.card_product, pow_three]
    exact Nat.mul_le_mul hAn.le (Nat.mul_le_mul hAn.le hAn.le)
  have hIM : I.card * M ≤ n ^ 3 * M := Nat.mul_le_mul_right _ hIc
  have : (S.card : ℤ) ≤ A.card + (I.card * M + I.card * M) := by exact_mod_cast (by omega)
  have : (n : ℤ) + 2 * (n ^ 3 * M) < S.card := by exact_mod_cast (by linarith)
  have : (I.card : ℤ) * M ≤ n ^ 3 * M := by exact_mod_cast hIM
  have : (A.card : ℤ) < n := by exact_mod_cast hAn
  linarith

/-- Large sets of affine dimension `< k` contain `n`-point distinct-distance subsets. -/
def Stmt (d k : ℕ) : Prop :=
  ∀ n, ∃ M, ∀ S : Finset (ℝ^d), affRank S < k → M ≤ S.card → GoodSet n S

/-- The same for sets lying on a sphere. -/
def StmtSph (d k : ℕ) : Prop :=
  ∀ n, ∃ M, ∀ S : Finset (ℝ^d), ∀ c : ℝ^d, ∀ R : ℝ, (∀ p ∈ S, dist p c = R) →
    affRank S < k → M ≤ S.card → GoodSet n S

lemma step_sph (k : ℕ) (ih : Stmt d k) : StmtSph d (k + 1) := by
  intro n
  obtain ⟨M, hM⟩ := ih n
  refine ⟨n + 2 * n ^ 3 * M + 1, fun S c R hSc hrk hcard => ?_⟩
  by_contra hG
  obtain ⟨x, hx, y, hy, z, hz, h | h⟩ := core S n M hG hcard
  · obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt h)
    have hxy : x ≠ y := (Finset.mem_filter.mp hq).2.1
    have hlt := affRank_lt (Finset.filter_subset _ S) x y 0
      (fun p hp => by rw [(Finset.mem_filter.mp hp).2.2]; ring) hx
      (by rw [dist_self]; have := dist_pos.mpr hxy; nlinarith) ⟨q, hq⟩
    exact hG (goodSet_mono (hM (S.filter (fun p => x ≠ y ∧ dist p x = dist p y)) (by omega) h.le)
      (Finset.filter_subset _ S))
  · obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt h)
    have hyz : y ≠ z := (Finset.mem_filter.mp hq).2.1
    have hlt := affRank_lt (Finset.filter_subset _ S) x c (dist y z ^ 2 - R ^ 2)
      (fun p hp => by
        rw [(Finset.mem_filter.mp hp).2.2, hSc p (Finset.mem_filter.mp hp).1])
      hx (by rw [dist_self, hSc x hx]; have := dist_pos.mpr hyz; nlinarith) ⟨q, hq⟩
    exact hG (goodSet_mono (hM (S.filter (fun p => y ≠ z ∧ dist p x = dist y z)) (by omega) h.le)
      (Finset.filter_subset _ S))

lemma step (k : ℕ) (ih : Stmt d k) (ihs : StmtSph d (k + 1)) : Stmt d (k + 1) := by
  intro n
  obtain ⟨M1, hM1⟩ := ih n
  obtain ⟨M2, hM2⟩ := ihs n
  refine ⟨n + 2 * n ^ 3 * (M1 + M2) + 1, fun S hrk hcard => ?_⟩
  by_contra hG
  obtain ⟨x, hx, y, hy, z, hz, h | h⟩ := core S n (M1 + M2) hG hcard
  · obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt h)
    have hxy : x ≠ y := (Finset.mem_filter.mp hq).2.1
    have hlt := affRank_lt (Finset.filter_subset _ S) x y 0
      (fun p hp => by rw [(Finset.mem_filter.mp hp).2.2]; ring) hx
      (by rw [dist_self]; have := dist_pos.mpr hxy; nlinarith) ⟨q, hq⟩
    exact hG (goodSet_mono (hM1 (S.filter (fun p => x ≠ y ∧ dist p x = dist p y)) (by omega)
      (by omega)) (Finset.filter_subset _ S))
  · have hle := affRank_mono (Finset.filter_subset
      (fun p => y ≠ z ∧ dist p x = dist y z) S)
    exact hG (goodSet_mono (hM2 (S.filter (fun p => y ≠ z ∧ dist p x = dist y z)) x (dist y z)
      (fun p hp => (Finset.mem_filter.mp hp).2.2) (by omega) (by omega))
      (Finset.filter_subset _ S))

lemma stmt_all : ∀ k, Stmt d k
  | 0 => fun _ => ⟨0, fun _ h _ => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => step k (stmt_all k) (step_sph k (stmt_all k))

theorem f_isLeast (d n : ℕ) : IsLeast (cardSet d n) (f d n) := by
  have hne : (cardSet d n).Nonempty := by
    obtain ⟨M, hM⟩ := stmt_all (d := d) (d + 1) n
    refine ⟨M + n, Nat.le_add_left _ _, fun S hS => ?_⟩
    obtain ⟨A, hAS, hAc, hA⟩ := hM S (affRank_lt_succ S) (by omega)
    exact ⟨A, hAS, hAc, pairwise_of_distInj hA⟩
  exact ⟨Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩

end OpenProofs.Erdos1088
