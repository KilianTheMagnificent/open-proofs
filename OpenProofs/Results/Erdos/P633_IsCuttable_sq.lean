import FormalConjectures.ErdosProblems.«633»

/-!
# `Erdos633.IsCuttable.sq`

Upstream: `Erdos633.IsCuttable.sq` (category API), `FormalConjectures/ErdosProblems/633.lean` line 56.
Proof idea: write points of the plane in affine coordinates `A + s • (B - A) + t • (C - A)`
relative to `T = ABC`. For `(i, j) ∈ Fin n × Fin n` with `i + j < n` take the image of `T` under
the homothety `x ↦ (1/n) • x + c` onto the "upward" small triangle with lattice corner `(i, j)`;
for `i + j ≥ n` take the image under `x ↦ -(1/n) • x + c'` onto the "downward" small triangle with
lattice corner `(n - i, n - j)`. All pieces have side lengths `1/n` times those of `T`, so they are
congruent. Uniqueness of affine coordinates gives disjoint interiors, and a floor computation
shows that every point of `T` lies in some piece.
-/

open Affine
open scoped Congruent EuclideanGeometry Similar
open Erdos633

namespace OpenProofs.Erdos633

/-- `x ↦ r • x + c` as an affine map of the plane. -/
noncomputable def opHom633 (r : ℝ) (c : ℝ²) : ℝ² →ᵃ[ℝ] ℝ² where
  toFun x := r • x + c
  linear := r • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_add]
    abel

lemma opHom633_apply (r : ℝ) (c x : ℝ²) : opHom633 r c x = r • x + c := rfl

lemma opHom633_injective {r : ℝ} (hr : r ≠ 0) (c : ℝ²) : Function.Injective (opHom633 r c) := by
  intro x y h
  simp only [opHom633_apply, add_left_inj] at h
  exact smul_right_injective _ hr h

lemma dist_opHom633 (r : ℝ) (c x y : ℝ²) :
    dist (opHom633 r c x) (opHom633 r c y) = |r| * dist x y := by
  simp only [opHom633_apply, dist_eq_norm, add_sub_add_right_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs]

/-- Affine coordinates relative to the triangle `T`. -/
noncomputable def coord633 (T : Triangle ℝ ℝ²) (s t : ℝ) : ℝ² :=
  T.points 0 + s • (T.points 1 - T.points 0) + t • (T.points 2 - T.points 0)

lemma coord633_sum (T : Triangle ℝ ℝ²) (s t : ℝ) :
    ∑ i, ![1 - s - t, s, t] i • T.points i = coord633 T s t := by
  simp only [Fin.sum_univ_three, coord633, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  exact by module

lemma coord633_inj {T : Triangle ℝ ℝ²} {s t s' t' : ℝ} (h : coord633 T s t = coord633 T s' t') :
    s = s' ∧ t = t' := by
  have key := T.independent.eq_of_sum_eq_sum (s := Finset.univ) (w₁ := ![1 - s - t, s, t])
    (w₂ := ![1 - s' - t', s', t']) (by simp [Fin.sum_univ_three]; ring) (by rw [coord633_sum,
      coord633_sum, h])
  exact ⟨by simpa using key 1 (by simp), by simpa using key 2 (by simp)⟩

lemma mem_closedInterior_iff633 {T : Triangle ℝ ℝ²} {x : ℝ²} :
    x ∈ T.closedInterior ↔ ∃ s t, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ coord633 T s t = x := by
  constructor
  · rintro ⟨w, hw, hw01, rfl⟩
    have hw' := hw
    rw [Fin.sum_univ_three] at hw'
    refine ⟨w 1, w 2, (hw01 1).1, (hw01 2).1, by linarith [(hw01 0).1], ?_⟩
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, Fin.sum_univ_three, coord633]
    have : w 0 = 1 - w 1 - w 2 := by linarith
    rw [this]
    exact by module
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    have hsum : ∑ i, ![1 - s - t, s, t] i = 1 := by simp [Fin.sum_univ_three]; ring
    refine ⟨![1 - s - t, s, t], hsum, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp <;> constructor <;> linarith
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum, coord633_sum]

lemma coord633_of_mem_interior {T : Triangle ℝ ℝ²} {x : ℝ²} (hx : x ∈ T.interior) :
    ∃ s t, 0 < s ∧ 0 < t ∧ s + t < 1 ∧ coord633 T s t = x := by
  obtain ⟨w, hw, hw01, rfl⟩ := hx
  have hw' := hw
  rw [Fin.sum_univ_three] at hw'
  refine ⟨w 1, w 2, (hw01 1).1, (hw01 2).1, by linarith [(hw01 0).1], ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, Fin.sum_univ_three, coord633]
  have : w 0 = 1 - w 1 - w 2 := by linarith
  rw [this]
  exact by module

/-- The affine map sending `T` onto the small triangle with index `p`. -/
noncomputable def piece633 (T : Triangle ℝ ℝ²) (n : ℕ) (p : Fin n × Fin n) : ℝ² →ᵃ[ℝ] ℝ² :=
  if (p.1 : ℕ) + (p.2 : ℕ) < n then
    opHom633 (1 / n) (coord633 T ((p.1 : ℕ) / n) ((p.2 : ℕ) / n) - (1 / n : ℝ) • T.points 0)
  else
    opHom633 (-(1 / n))
      (coord633 T ((n - (p.1 : ℕ)) / n) ((n - (p.2 : ℕ)) / n) + (1 / n : ℝ) • T.points 0)

lemma piece633_injective {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) (p : Fin n × Fin n) :
    Function.Injective (piece633 T n p) := by
  have : (1 / n : ℝ) ≠ 0 := by simp [hn]
  unfold piece633
  split_ifs
  · exact opHom633_injective this _
  · exact opHom633_injective (neg_ne_zero.2 this) _

lemma dist_piece633 (T : Triangle ℝ ℝ²) (n : ℕ) (p : Fin n × Fin n) (x y : ℝ²) :
    dist (piece633 T n p x) (piece633 T n p y) = (1 / n) * dist x y := by
  have h : |(1 / n : ℝ)| = 1 / n := abs_of_nonneg (by positivity)
  unfold piece633
  split_ifs
  · rw [dist_opHom633, h]
  · rw [dist_opHom633, abs_neg, h]

lemma piece633_up {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) {p : Fin n × Fin n}
    (h : (p.1 : ℕ) + (p.2 : ℕ) < n) (s t : ℝ) :
    piece633 T n p (coord633 T s t) = coord633 T (((p.1 : ℕ) + s) / n) (((p.2 : ℕ) + t) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [piece633, h, if_true, opHom633_apply, coord633]
  simp only [add_div, smul_add, smul_sub, add_smul, smul_smul]
  field_simp
  exact by module

lemma piece633_down {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) {p : Fin n × Fin n}
    (h : ¬ (p.1 : ℕ) + (p.2 : ℕ) < n) (s t : ℝ) :
    piece633 T n p (coord633 T s t) =
      coord633 T ((n - (p.1 : ℕ) - s) / n) ((n - (p.2 : ℕ) - t) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [piece633, h, if_false, opHom633_apply, coord633]
  simp only [sub_div, smul_add, smul_sub, smul_smul, sub_smul, neg_smul]
  field_simp
  exact by module

lemma nat_eq_of_frac633 {a b : ℕ} {s s' : ℝ} (hs : 0 < s) (hs1 : s < 1) (hs' : 0 < s')
    (hs1' : s' < 1) (h : (a : ℝ) + s = b + s') : a = b := by
  have h1 : a < b + 1 := by exact_mod_cast (show (a : ℝ) < b + 1 by linarith)
  have h2 : b < a + 1 := by exact_mod_cast (show (b : ℝ) < a + 1 by linarith)
  omega

lemma frac_sum_eq_one633 {a b n : ℕ} {u : ℝ} (hu0 : 0 < u) (hu2 : u < 2)
    (h : (a : ℝ) + b + u = n) : u = 1 := by
  have h1 : a + b < n := by exact_mod_cast (show ((a + b : ℕ) : ℝ) < n by push_cast; linarith)
  have h2 : n < a + b + 2 := by
    exact_mod_cast (show (n : ℝ) < ((a + b + 2 : ℕ) : ℝ) by push_cast; linarith)
  have h3 : ((a + b + 1 : ℕ) : ℝ) = n := by exact_mod_cast (show a + b + 1 = n by omega)
  push_cast at h3
  linarith

lemma disjoint_pieces633 {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) {p q : Fin n × Fin n}
    (hpq : p ≠ q) : Disjoint (piece633 T n p '' T.interior) (piece633 T n q '' T.interior) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Set.disjoint_left]
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hyz⟩
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := coord633_of_mem_interior hy
  obtain ⟨s', t', hs', ht', hst', rfl⟩ := coord633_of_mem_interior hz
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := q
  apply hpq
  by_cases hp : i + j < n <;> by_cases hq : i' + j' < n
  · rw [piece633_up (p := (⟨i, hi⟩, ⟨j, hj⟩)) hn hp, piece633_up (p := (⟨i', hi'⟩, ⟨j', hj'⟩)) hn hq] at hyz
    obtain ⟨e1, e2⟩ := coord633_inj hyz
    rw [div_left_inj' hn'] at e1 e2
    simp only at e1 e2
    have := nat_eq_of_frac633 hs (by linarith) hs' (by linarith) e1.symm
    have := nat_eq_of_frac633 ht (by linarith) ht' (by linarith) e2.symm
    subst_vars
    rfl
  · rw [piece633_up (p := (⟨i, hi⟩, ⟨j, hj⟩)) hn hp, piece633_down (p := (⟨i', hi'⟩, ⟨j', hj'⟩)) hn hq] at hyz
    obtain ⟨e1, e2⟩ := coord633_inj hyz
    rw [div_left_inj' hn'] at e1 e2
    simp only at e1 e2
    have u1 := frac_sum_eq_one633 (a := i) (b := i') (n := n) (u := s + s') (by linarith)
      (by linarith) (by linarith)
    have u2 := frac_sum_eq_one633 (a := j) (b := j') (n := n) (u := t + t') (by linarith)
      (by linarith) (by linarith)
    linarith
  · rw [piece633_down (p := (⟨i, hi⟩, ⟨j, hj⟩)) hn hp, piece633_up (p := (⟨i', hi'⟩, ⟨j', hj'⟩)) hn hq] at hyz
    obtain ⟨e1, e2⟩ := coord633_inj hyz
    rw [div_left_inj' hn'] at e1 e2
    simp only at e1 e2
    have u1 := frac_sum_eq_one633 (a := i) (b := i') (n := n) (u := s + s') (by linarith)
      (by linarith) (by linarith)
    have u2 := frac_sum_eq_one633 (a := j) (b := j') (n := n) (u := t + t') (by linarith)
      (by linarith) (by linarith)
    linarith
  · rw [piece633_down (p := (⟨i, hi⟩, ⟨j, hj⟩)) hn hp, piece633_down (p := (⟨i', hi'⟩, ⟨j', hj'⟩)) hn hq] at hyz
    obtain ⟨e1, e2⟩ := coord633_inj hyz
    rw [div_left_inj' hn'] at e1 e2
    simp only at e1 e2
    have := nat_eq_of_frac633 hs (by linarith) hs' (by linarith) (by linarith : (i : ℝ) + s = i' + s')
    have := nat_eq_of_frac633 ht (by linarith) ht' (by linarith) (by linarith : (j : ℝ) + t = j' + t')
    subst_vars
    rfl

lemma hit_up633 {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) (p : Fin n × Fin n)
    (h : (p.1 : ℕ) + (p.2 : ℕ) < n) {s t s' t' : ℝ} (hs' : 0 ≤ s') (ht' : 0 ≤ t')
    (hst' : s' + t' ≤ 1) (e1 : ((p.1 : ℕ) : ℝ) + s' = n * s) (e2 : ((p.2 : ℕ) : ℝ) + t' = n * t) :
    coord633 T s t ∈ piece633 T n p '' T.closedInterior := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨coord633 T s' t', mem_closedInterior_iff633.2 ⟨s', t', hs', ht', hst', rfl⟩, ?_⟩
  rw [piece633_up hn h, e1, e2, mul_div_cancel_left₀ _ hn', mul_div_cancel_left₀ _ hn']

lemma hit_down633 {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) (p : Fin n × Fin n)
    (h : ¬ (p.1 : ℕ) + (p.2 : ℕ) < n) {s t s' t' : ℝ} (hs' : 0 ≤ s') (ht' : 0 ≤ t')
    (hst' : s' + t' ≤ 1) (e1 : (n : ℝ) - ((p.1 : ℕ) : ℝ) - s' = n * s)
    (e2 : (n : ℝ) - ((p.2 : ℕ) : ℝ) - t' = n * t) :
    coord633 T s t ∈ piece633 T n p '' T.closedInterior := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨coord633 T s' t', mem_closedInterior_iff633.2 ⟨s', t', hs', ht', hst', rfl⟩, ?_⟩
  rw [piece633_down hn h, e1, e2, mul_div_cancel_left₀ _ hn', mul_div_cancel_left₀ _ hn']

lemma union_pieces633 {T : Triangle ℝ ℝ²} {n : ℕ} (hn : n ≠ 0) :
    ⋃ p, piece633 T n p '' T.closedInterior = T.closedInterior := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply Set.Subset.antisymm
  · rw [Set.iUnion_subset_iff]
    rintro p _ ⟨y, hy, rfl⟩
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := mem_closedInterior_iff633.1 hy
    rw [mem_closedInterior_iff633]
    have hi : ((p.1 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast p.1.isLt
    have hj : ((p.2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast p.2.isLt
    by_cases h : (p.1 : ℕ) + (p.2 : ℕ) < n
    · rw [piece633_up hn h]
      refine ⟨_, _, by positivity, by positivity, ?_, rfl⟩
      rw [← add_div, div_le_one hn0]
      have : ((p.1 : ℕ) : ℝ) + ((p.2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith
    · rw [piece633_down hn h]
      refine ⟨_, _, div_nonneg (by linarith) hn0.le, div_nonneg (by linarith) hn0.le, ?_, rfl⟩
      rw [← add_div, div_le_one hn0]
      have : (n : ℝ) ≤ ((p.1 : ℕ) : ℝ) + ((p.2 : ℕ) : ℝ) := by exact_mod_cast not_lt.mp h
      linarith
  · intro x hx
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := mem_closedInterior_iff633.1 hx
    rw [Set.mem_iUnion]
    have ha : 0 ≤ (n : ℝ) * s := by positivity
    have hb : 0 ≤ (n : ℝ) * t := by positivity
    have hab : (n : ℝ) * s + n * t ≤ n := by nlinarith
    set a := (n : ℝ) * s with ha_def
    set b := (n : ℝ) * t with hb_def
    have hi1 : ((⌊a⌋₊ : ℕ) : ℝ) ≤ a := Nat.floor_le ha
    have hi2 : a < ((⌊a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
    have hj1 : ((⌊b⌋₊ : ℕ) : ℝ) ≤ b := Nat.floor_le hb
    have hj2 : b < ((⌊b⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one b
    set i := ⌊a⌋₊
    set j := ⌊b⌋₊
    have hijn : i + j ≤ n := by
      exact_mod_cast (show ((i + j : ℕ) : ℝ) ≤ n by push_cast; linarith)
    by_cases hc : a + b ≤ i + j + 1
    · by_cases hlt : i + j < n
      · exact ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hit_up633 hn _ hlt (s' := a - i) (t' := b - j)
          (by linarith) (by linarith) (by linarith) (by simp only; linarith) (by simp only; linarith)⟩
      · have hsum : ((i + j : ℕ) : ℝ) = n := by exact_mod_cast (show i + j = n by omega)
        push_cast at hsum
        have hai : a = i := by linarith
        have hbj : b = j := by linarith
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          have hk' : (j : ℝ) = k + 1 := by exact_mod_cast hk
          refine ⟨(⟨0, by omega⟩, ⟨k, by omega⟩), hit_up633 hn _ (by simp; omega) (s' := 0)
            (t' := 1) le_rfl zero_le_one (by norm_num) ?_ ?_⟩
          · simp only [Nat.cast_zero, zero_add]
            rw [← ha_def, hai, h0]
            simp
          · simp only
            rw [← hb_def]
            linarith
        · obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
          have hk' : (i : ℝ) = k + 1 := by exact_mod_cast hk
          refine ⟨(⟨k, by omega⟩, ⟨j, by omega⟩), hit_up633 hn _ (by simp; omega) (s' := 1)
            (t' := 0) zero_le_one le_rfl (by norm_num) ?_ ?_⟩
          · simp only
            rw [← ha_def]
            linarith
          · simp only [add_zero]
            rw [← hb_def, hbj]
    · push Not at hc
      have hlt : i + j + 1 < n := by
        exact_mod_cast (show ((i + j + 1 : ℕ) : ℝ) < n by push_cast; linarith)
      have hci : ((n - 1 - i : ℕ) : ℝ) + i + 1 = n := by
        exact_mod_cast (show n - 1 - i + i + 1 = n by omega)
      have hcj : ((n - 1 - j : ℕ) : ℝ) + j + 1 = n := by
        exact_mod_cast (show n - 1 - j + j + 1 = n by omega)
      refine ⟨(⟨n - 1 - i, by omega⟩, ⟨n - 1 - j, by omega⟩), hit_down633 hn _ (by simp; omega)
        (s' := i + 1 - a) (t' := j + 1 - b) (by linarith) (by linarith) (by linarith) ?_ ?_⟩
      · simp only
        rw [← ha_def]
        linarith
      · simp only
        rw [← hb_def]
        linarith

variable {n : ℕ} {T : Triangle ℝ ℝ²}
variable (n T) in

theorem IsCuttable.sq (hn : n ≠ 0) : IsCuttable (n ^ 2) T := by
  let e : Fin (n ^ 2) ≃ Fin n × Fin n := (finCongr (pow_two n)).trans finProdFinEquiv.symm
  refine ⟨fun k => T.map (piece633 T n (e k)) (piece633_injective hn _), ?_, ?_, ?_⟩
  · intro k l
    rw [congruent_iff_dist_eq]
    intro a b
    simp only [Simplex.map_points, Function.comp_apply, dist_piece633]
  · intro k l hkl
    simp only [Simplex.interior_map]
    exact disjoint_pieces633 hn (e.injective.ne hkl)
  · simp only [Simplex.closedInterior_map]
    rw [e.surjective.iUnion_comp (fun p => piece633 T n p '' T.closedInterior)]
    exact union_pieces633 hn

end OpenProofs.Erdos633
