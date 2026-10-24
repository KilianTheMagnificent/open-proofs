import FormalConjectures.Mathoverflow.«17560»

/-!
# `Mathoverflow17560.mathoverflow_17560.variants.with_5`

Upstream: `Mathoverflow17560.mathoverflow_17560.variants.with_5` (category textbook), `FormalConjectures/Mathoverflow/17560.lean` line 51.
Proof idea: a case of the six exponentials theorem, proved by Laurent's interpolation
determinant with real analysis only. If `x = p/q` is rational, `2^p = m^q` forces `q ∣ p`
(2-adic valuation). If `x` is irrational, take `N = P^12` frequencies `k₁ + k₂ x`
(`k₁, k₂ < P^6`, distinct by irrationality) and `N` points `h₁ log 2 + h₂ log 3 + h₃ log 5`
(`hᵢ < P^4`, distinct by unique factorization). The entries `exp (z w)` of the `N × N` matrix are
the integers `2^(k₁h₁)⋯a^(k₂h₁)⋯` (`a = 2^x`, ...), so its determinant is an integer. It is
nonzero: an exponential sum with `N` distinct real frequencies has fewer than `N` real zeros
(induction with Rolle's theorem). Expanding `det = ∑ σ sign σ exp (S σ)`, the Taylor terms of order
`< N(N-1)/2` cancel (each is a sum of determinants with two equal columns), so
`|det| ≤ N! · 2 T^M / M!` with `M = P^23`, `T = 7(1+|x|) P^22`, which is `< 1` for
`P ≥ 42(1+|x|)`. Contradiction.
-/

open Mathoverflow17560

namespace OpenProofs.Mathoverflow17560

/-- Rolle counting: a differentiable function vanishing on `Z` has a derivative vanishing on a
set with at most one point fewer (all of them below some point of `Z`). -/
lemma mo17560_rolle_aux (f : ℝ → ℝ) (hf : Differentiable ℝ f) (Z : Finset ℝ) :
    (∀ z ∈ Z, f z = 0) → ∃ Z' : Finset ℝ, Z.card ≤ Z'.card + 1 ∧
      (∀ c ∈ Z', deriv f c = 0) ∧ (∀ c ∈ Z', ∃ z ∈ Z, c < z) := by
  induction Z using Finset.induction_on_max with
  | empty => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | insert a s ha ih =>
    intro hz
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hs : ∀ z ∈ s, f z = 0 := fun z hz' => hz z (Finset.mem_insert_of_mem hz')
    obtain ⟨Z0, h1, h2, h3⟩ := ih hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp, by simp⟩
    · have hb : s.max' hne < a := ha _ (s.max'_mem hne)
      obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero hb hf.continuous.continuousOn
        (by rw [hs _ (s.max'_mem hne), hz a (Finset.mem_insert_self a s)])
      have hcZ0 : c ∉ Z0 := by
        intro hc'
        obtain ⟨z, hz', hcz⟩ := h3 c hc'
        have := s.le_max' z hz'
        linarith [hc.1]
      refine ⟨insert c Z0, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem has, Finset.card_insert_of_notMem hcZ0]; omega
      · intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hc0
        · exact h2 d hd
      · intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact ⟨a, Finset.mem_insert_self a s, hc.2⟩
        · obtain ⟨z, hz', hdz⟩ := h3 d hd
          exact ⟨z, Finset.mem_insert_of_mem hz', hdz⟩

/-- Zero estimate: an exponential sum with distinct real frequencies vanishing at at least as
many points as it has terms is identically zero. -/
lemma mo17560_exp_sum_zero {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    ∀ (w p : ι → ℝ), Set.InjOn w s → ∀ Z : Finset ℝ, s.card ≤ Z.card →
      (∀ t ∈ Z, ∑ i ∈ s, p i * Real.exp (w i * t) = 0) → ∀ i ∈ s, p i = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i0 s hi0 ih =>
    intro w p hw Z hZ hF
    set G : ℝ → ℝ := fun t => ∑ i ∈ insert i0 s, p i * Real.exp ((w i - w i0) * t) with hG
    have hGZ : ∀ t ∈ Z, G t = 0 := by
      intro t ht
      have : G t = Real.exp (-(w i0 * t)) * ∑ i ∈ insert i0 s, p i * Real.exp (w i * t) := by
        simp only [hG, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
      rw [this, hF t ht, mul_zero]
    have hGd : ∀ t, HasDerivAt G
        (∑ i ∈ s, (p i * (w i - w i0)) * Real.exp ((w i - w i0) * t)) t := by
      intro t
      have h : HasDerivAt G
          (∑ i ∈ insert i0 s, (p i * (w i - w i0)) * Real.exp ((w i - w i0) * t)) t := by
        exact HasDerivAt.fun_sum (u := insert i0 s)
          (A := fun i t => p i * Real.exp ((w i - w i0) * t))
          (A' := fun i => (p i * (w i - w i0)) * Real.exp ((w i - w i0) * t)) (x := t)
          (fun i _ => by
            have := (((hasDerivAt_id t).const_mul (w i - w i0)).exp).const_mul (p i)
            simp only [id_eq, mul_one] at this
            exact this.congr_deriv (by ring))
      rwa [Finset.sum_insert hi0, sub_self, mul_zero, zero_mul, zero_add] at h
    obtain ⟨Z', hZ', hZ'0⟩ : ∃ Z' : Finset ℝ, Z.card ≤ Z'.card + 1 ∧ (∀ c ∈ Z', deriv G c = 0) := by
      obtain ⟨Z', h1, h2, -⟩ :=
        mo17560_rolle_aux G (fun t => (hGd t).differentiableAt) Z hGZ
      exact ⟨Z', h1, h2⟩
    rw [Finset.card_insert_of_notMem hi0] at hZ
    have hs : ∀ i ∈ s, p i * (w i - w i0) = 0 := by
      refine ih (fun i => w i - w i0) (fun i => p i * (w i - w i0)) ?_ Z' (by omega) ?_
      · intro i hi j hj hij
        exact hw (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) (by simpa using hij)
      · intro t ht
        rw [← (hGd t).deriv]; exact hZ'0 t ht
    have hs' : ∀ i ∈ s, p i = 0 := fun i hi => by
      have hne : w i - w i0 ≠ 0 := by
        intro h
        have := hw (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self _ _) (sub_eq_zero.mp h)
        exact hi0 (this ▸ hi)
      exact (mul_eq_zero.mp (hs i hi)).resolve_right hne
    obtain ⟨t, ht⟩ : Z.Nonempty := Finset.card_pos.mp (by omega)
    have h0 := hF t ht
    rw [Finset.sum_insert hi0, Finset.sum_eq_zero (fun i hi => by rw [hs' i hi, zero_mul]),
      add_zero] at h0
    have hp0 : p i0 = 0 := (mul_eq_zero.mp h0).resolve_right (Real.exp_pos _).ne'
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hp0
    · exact hs' i hi

/-- The interpolation determinant `det (exp (z j * w i))` is nonzero for distinct `w`, `z`. -/
lemma mo17560_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (w z : ι → ℝ)
    (hw : Function.Injective w) (hz : Function.Injective z) :
    (Matrix.of fun j i => Real.exp (z j * w i)).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h
  apply hv
  funext i
  refine mo17560_exp_sum_zero Finset.univ w v hw.injOn (Finset.univ.image z) ?_ ?_ i
    (Finset.mem_univ i)
  · rw [Finset.card_image_of_injective _ hz]
  · intro t ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ht
    have := congrFun hMv j
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm (w i)]; ring

lemma mo17560_card_sq_le (s : Finset ℕ) : s.card * s.card ≤ 2 * ∑ v ∈ s, v + s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (ha x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has]
    nlinarith

/-- The low-order Taylor coefficients of the interpolation determinant vanish. -/
lemma mo17560_alt_sum_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (w z : ι → ℝ) (m : ℕ)
    (hm : 2 * m + Fintype.card ι < Fintype.card ι * Fintype.card ι) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∑ i, w i * z (σ i)) ^ m = 0 := by
  have key : ∀ g : Fin m → ι,
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, z (σ (g k)) = 0 := by
    intro g
    set c : ι → ℕ := fun i => (Finset.univ.filter fun k => g k = i).card with hc
    have hsum : ∑ i, c i = m := by
      have := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := Finset.univ)
        (by simp [Set.MapsTo])
      simpa [hc] using this.symm
    have hprod : ∀ σ : Equiv.Perm ι, ∏ k, z (σ (g k)) = ∏ i, z (σ i) ^ c i := by
      intro σ
      rw [← Finset.prod_fiberwise Finset.univ g (fun k => z (σ (g k)))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]),
        Finset.prod_const]
    have hninj : ¬ Function.Injective c := by
      intro hinj
      have h1 := mo17560_card_sq_le (Finset.univ.image c)
      rw [Finset.card_image_of_injective _ hinj, Finset.sum_image (fun i _ j _ h => hinj h),
        hsum, Finset.card_univ] at h1
      omega
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
      by_contra hcon
      push Not at hcon
      exact hninj fun i j h => hcon i j h
    have hdet := Matrix.det_zero_of_column_eq (M := Matrix.of fun a b => z a ^ c b) hne
      (fun k => by simp [hij])
    rw [Matrix.det_apply] at hdet
    rw [← hdet]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hprod σ, Units.smul_def, zsmul_eq_mul]
    simp
  calc ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∑ i, w i * z (σ i)) ^ m
      = ∑ σ : Equiv.Perm ι, ∑ g : Fin m → ι,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ k, w (g k)) * ∏ k, z (σ (g k))) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Fin.prod_const, Fintype.prod_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.prod_mul_distrib]
    _ = ∑ g : Fin m → ι, (∏ k, w (g k)) *
          ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ k, z (σ (g k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ = 0 := Finset.sum_eq_zero fun g _ => by rw [key g, mul_zero]

lemma mo17560_exp_rem (S T : ℝ) (M : ℕ) (hS : |S| ≤ T) (hTM : T / (M + 1) ≤ 1 / 2) :
    |Real.exp S - ∑ m ∈ Finset.range M, S ^ m / m.factorial| ≤ T ^ M / M.factorial * 2 := by
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have h := Complex.exp_bound' (x := (S : ℂ)) (n := M) (by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |S| / (M.succ : ℝ) = |S| / (M + 1) := by push_cast; ring
      _ ≤ T / (M + 1) := by gcongr
      _ ≤ 1 / 2 := hTM)
  have hc : Complex.exp (S : ℂ) - ∑ m ∈ Finset.range M, (S : ℂ) ^ m / m.factorial =
      ((Real.exp S - ∑ m ∈ Finset.range M, S ^ m / m.factorial : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
  calc _ ≤ |S| ^ M / M.factorial * 2 := h
    _ ≤ T ^ M / M.factorial * 2 := by gcongr

lemma mo17560_det_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (w z : ι → ℝ) (M : ℕ) (T : ℝ)
    (hM : 2 * M + Fintype.card ι ≤ Fintype.card ι * Fintype.card ι)
    (hT : ∀ σ : Equiv.Perm ι, |∑ i, w i * z (σ i)| ≤ T) (hTM : T / (M + 1) ≤ 1 / 2) :
    |(Matrix.of fun j i => Real.exp (z j * w i)).det| ≤
      ((Fintype.card ι).factorial : ℝ) * (T ^ M / M.factorial * 2) := by
  set S : Equiv.Perm ι → ℝ := fun σ => ∑ i, w i * z (σ i) with hS
  have hdet : (Matrix.of fun j i => Real.exp (z j * w i)).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (Real.exp (S σ) - ∑ m ∈ Finset.range M, S σ ^ m / m.factorial) := by
    have h0 : ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ m ∈ Finset.range M, S σ ^ m / m.factorial = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm' := Finset.mem_range.mp hm
      have := mo17560_alt_sum_pow w z m (by nlinarith)
      rw [show (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * (S σ ^ m / m.factorial)) =
          (∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∑ i, w i * z (σ i)) ^ m) /
            m.factorial by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun σ _ => by ring]
      rw [this, zero_div]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, h0, sub_zero, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    congr 1
    simp only [Matrix.of_apply, hS, ← Real.exp_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hdet]
  calc _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) *
        (Real.exp (S σ) - ∑ m ∈ Finset.range M, S σ ^ m / m.factorial)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Equiv.Perm ι, (T ^ M / M.factorial * 2) := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [abs_mul]
        have : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [this, one_mul]
        exact mo17560_exp_rem (S σ) T M (hT σ) hTM
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- Abstract form of the interpolation-determinant argument. -/
lemma mo17560_abstract {ι : Type*} [Fintype ι] [DecidableEq ι] (w z : ι → ℝ)
    (hw : Function.Injective w) (hz : Function.Injective z) (e : ι → ι → ℤ)
    (he : ∀ j i, Real.exp (z j * w i) = e j i) (M : ℕ) (T : ℝ)
    (hM : 2 * M + Fintype.card ι ≤ Fintype.card ι * Fintype.card ι)
    (hT : ∀ σ : Equiv.Perm ι, |∑ i, w i * z (σ i)| ≤ T) (hTM : T / (M + 1) ≤ 1 / 2)
    (hsmall : ((Fintype.card ι).factorial : ℝ) * (T ^ M / M.factorial * 2) < 1) : False := by
  have hA : (Matrix.of fun j i => Real.exp (z j * w i)) =
      (Matrix.of e).map (fun a : ℤ => (a : ℝ)) := by
    ext j i; simp [he]
  have hne := mo17560_det_ne_zero w z hw hz
  have hb := mo17560_det_bound w z M T hM hT hTM
  rw [hA, ← Int.cast_det] at hne hb
  have h1 : (1 : ℝ) ≤ |((Matrix.of e).det : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by exact_mod_cast hne)
  linarith

lemma mo17560_numeric (u : ℝ) (hu : 1 ≤ u) (P : ℕ) (hP3 : 3 ≤ P) (hPu : 42 * u ≤ P) :
    (((P ^ 12).factorial : ℕ) : ℝ) *
      ((7 * u * (P : ℝ) ^ 22) ^ (P ^ 23) / ((P ^ 23).factorial : ℝ) * 2) < 1 := by
  set M := P ^ 23 with hMdef
  set T : ℝ := 7 * u * (P : ℝ) ^ 22 with hTdef
  have hP0 : (0 : ℝ) < P := by have : (3 : ℝ) ≤ P := by exact_mod_cast hP3
                               linarith
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; push_cast; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hfact : (M : ℝ) ^ M / M.factorial ≤ Real.exp M :=
    Real.pow_div_factorial_le_exp _ hMpos.le M
  have he : Real.exp (M : ℝ) ≤ 3 ^ M := by
    calc Real.exp M = Real.exp 1 ^ M := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 3 ^ M := pow_le_pow_left₀ (Real.exp_pos 1).le
          (by linarith [Real.exp_one_lt_d9]) M
  have h1 : T ^ M / M.factorial ≤ (1 / 2) ^ M := by
    have hMf : (0 : ℝ) < M.factorial := by positivity
    have h3T : 3 * T / M ≤ 1 / 2 := by
      rw [div_le_iff₀ hMpos, hTdef, hMdef]
      push_cast
      have h22 : (0 : ℝ) < (P : ℝ) ^ 22 := by positivity
      have : (P : ℝ) ^ 23 = (P : ℝ) ^ 22 * P := by ring
      rw [this]
      nlinarith
    calc T ^ M / M.factorial = (T / M) ^ M * ((M : ℝ) ^ M / M.factorial) := by
          rw [div_pow]; field_simp
      _ ≤ (T / M) ^ M * 3 ^ M := by
          gcongr
          exact hfact.trans he
      _ = (3 * T / M) ^ M := by rw [← mul_pow]; ring_nf
      _ ≤ (1 / 2) ^ M := by gcongr
  have h2 : (P ^ 12).factorial * 2 < 2 ^ M := by
    have hP2 : P < 2 ^ P := Nat.lt_two_pow_self
    have hN : (P ^ 12).factorial ≤ 2 ^ (12 * P ^ 13) := by
      calc (P ^ 12).factorial ≤ (P ^ 12) ^ (P ^ 12) := Nat.factorial_le_pow _
        _ ≤ ((2 ^ P) ^ 12) ^ (P ^ 12) := by gcongr
        _ = 2 ^ (12 * P ^ 13) := by rw [← pow_mul, ← pow_mul]; ring_nf
    have hexp : 12 * P ^ 13 + 1 < P ^ 23 := by
      have h10 : 3 ^ 10 ≤ P ^ 10 := Nat.pow_le_pow_left hP3 10
      have h13 : 1 ≤ P ^ 13 := Nat.one_le_pow _ _ (by omega)
      have : P ^ 23 = P ^ 10 * P ^ 13 := by ring
      rw [this]
      nlinarith
    calc (P ^ 12).factorial * 2 ≤ 2 ^ (12 * P ^ 13) * 2 := by gcongr
      _ = 2 ^ (12 * P ^ 13 + 1) := by ring
      _ < 2 ^ M := Nat.pow_lt_pow_right (by norm_num) hexp
  have h2' : (((P ^ 12).factorial : ℕ) : ℝ) * 2 < 2 ^ M := by exact_mod_cast h2
  calc (((P ^ 12).factorial : ℕ) : ℝ) * (T ^ M / M.factorial * 2)
      ≤ (((P ^ 12).factorial : ℕ) : ℝ) * ((1 / 2) ^ M * 2) := by gcongr
    _ = (((P ^ 12).factorial : ℕ) : ℝ) * 2 / 2 ^ M := by rw [one_div_pow]; ring
    _ < 1 := by rw [div_lt_one (by positivity)]; exact h2'

lemma mo17560_rational {x : ℝ} (q : ℚ) (hq : (q : ℝ) = x) (m : ℕ) (hm : (2 : ℝ) ^ x = m) :
    ∃ n : ℕ, x = n := by
  have hx0 : 0 ≤ x := by
    by_contra h
    push Not at h
    have h1 : (2 : ℝ) ^ x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) h
    have h2 : (0 : ℝ) < 2 ^ x := Real.rpow_pos_of_pos (by norm_num) x
    rw [hm] at h1 h2
    have h1' : m < 1 := by exact_mod_cast h1
    have h2' : 0 < m := by exact_mod_cast h2
    omega
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ q := hq ▸ hx0
    exact_mod_cast this
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q.num = n := ⟨q.num.toNat, (Int.toNat_of_nonneg hnum).symm⟩
  have hxd : x * q.den = n := by
    have h : (q * q.den : ℚ) = n := by rw [Rat.mul_den_eq_num, hn, Int.cast_natCast]
    rw [← hq]
    exact_mod_cast h
  have h2n : (2 : ℝ) ^ n = (m : ℝ) ^ q.den := by
    rw [← hm, ← Real.rpow_mul_natCast (by norm_num), hxd, Real.rpow_natCast]
  have h2n' : 2 ^ n = m ^ q.den := by exact_mod_cast h2n
  have hfac := congrArg (fun k => k.factorization 2) h2n'
  simp [Nat.factorization_pow, Nat.prime_two.factorization_self] at hfac
  refine ⟨m.factorization 2, ?_⟩
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have : x * q.den = (m.factorization 2 : ℝ) * q.den := by
    rw [hxd, hfac]; push_cast; ring
  exact mul_right_cancel₀ hden.ne' this

lemma mo17560_smooth_inj (a b c a' b' c' : ℕ)
    (h : 2 ^ a * 3 ^ b * 5 ^ c = 2 ^ a' * 3 ^ b' * 5 ^ c') : a = a' ∧ b = b' ∧ c = c' := by
  have h2 := congrArg (fun k => k.factorization 2) h
  have h3 := congrArg (fun k => k.factorization 3) h
  have h5 := congrArg (fun k => k.factorization 5) h
  simp [Nat.factorization_mul, Nat.factorization_pow, Nat.prime_two.factorization,
    Nat.prime_three.factorization, Nat.prime_five.factorization] at h2 h3 h5
  exact ⟨h2, h3, h5⟩

/-- The irrational case: the interpolation determinant built from the frequencies
`k₁ + k₂ x` and the points `h₁ log 2 + h₂ log 3 + h₃ log 5` is a nonzero integer of absolute
value less than one. -/
lemma mo17560_irrational {x : ℝ} (hirr : Irrational x) (a b c : ℕ) (ha : (2 : ℝ) ^ x = a)
    (hb : (3 : ℝ) ^ x = b) (hc : (5 : ℝ) ^ x = c) : False := by
  have ha0 : (0 : ℝ) < a := ha ▸ Real.rpow_pos_of_pos (by norm_num) x
  have hb0 : (0 : ℝ) < b := hb ▸ Real.rpow_pos_of_pos (by norm_num) x
  have hc0 : (0 : ℝ) < c := hc ▸ Real.rpow_pos_of_pos (by norm_num) x
  have hla : Real.log a = x * Real.log 2 := by rw [← ha, Real.log_rpow (by norm_num)]
  have hlb : Real.log b = x * Real.log 3 := by rw [← hb, Real.log_rpow (by norm_num)]
  have hlc : Real.log c = x * Real.log 5 := by rw [← hc, Real.log_rpow (by norm_num)]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 + |x| := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; linarith [abs_nonneg x]
  obtain ⟨P, hP3, hPu⟩ : ∃ P : ℕ, 3 ≤ P ∧ 42 * u ≤ P :=
    ⟨⌈42 * u⌉₊ + 3, by omega, by push_cast; linarith [Nat.le_ceil (42 * u)]⟩
  have hP0 : (0 : ℝ) < P := by
    have : (3 : ℝ) ≤ P := by exact_mod_cast hP3
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P ^ 6 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ, H = P ^ 4 := ⟨_, rfl⟩
  have hcardι : Fintype.card (Fin K × Fin K) = P ^ 12 := by simp [hK]; ring
  have hcard : Fintype.card (Fin K × Fin K) = Fintype.card (Fin H × Fin H × Fin H) := by
    rw [hcardι]; simp [hH]; ring
  let E : Fin K × Fin K ≃ Fin H × Fin H × Fin H := Fintype.equivOfCardEq hcard
  let w : Fin K × Fin K → ℝ := fun i => ((i.1 : ℕ) : ℝ) + ((i.2 : ℕ) : ℝ) * x
  let zz : Fin H × Fin H × Fin H → ℝ := fun h =>
    ((h.1 : ℕ) : ℝ) * Real.log 2 + ((h.2.1 : ℕ) : ℝ) * Real.log 3 +
      ((h.2.2 : ℕ) : ℝ) * Real.log 5
  let z : Fin K × Fin K → ℝ := fun j => zz (E j)
  have hexp : ∀ (n : ℕ) (r : ℝ), 0 < r → Real.exp ((n : ℝ) * Real.log r) = r ^ n := by
    intro n r hr; rw [Real.exp_nat_mul, Real.exp_log hr]
  have hzz : ∀ h : Fin H × Fin H × Fin H, Real.exp (zz h) =
      ((2 ^ (h.1 : ℕ) * 3 ^ (h.2.1 : ℕ) * 5 ^ (h.2.2 : ℕ) : ℕ) : ℝ) := by
    intro h
    simp only [zz, Real.exp_add, hexp _ _ (by norm_num : (0 : ℝ) < 2),
      hexp _ _ (by norm_num : (0 : ℝ) < 3), hexp _ _ (by norm_num : (0 : ℝ) < 5)]
    push_cast; ring
  have hw : Function.Injective w := by
    rintro ⟨k1, k2⟩ ⟨k1', k2'⟩ hk
    simp only [w] at hk
    by_cases h2 : (k2 : ℕ) = k2'
    · have h1 : ((k1 : ℕ) : ℝ) = k1' := by rw [h2] at hk; linarith
      have h1' : (k1 : ℕ) = k1' := by exact_mod_cast h1
      rw [Prod.mk.injEq]; exact ⟨Fin.ext h1', Fin.ext h2⟩
    · exfalso
      have hm : ((k2 : ℕ) : ℤ) - (k2' : ℕ) ≠ 0 := by omega
      apply (hirr.mul_intCast hm).ne_int (((k1' : ℕ) : ℤ) - (k1 : ℕ))
      push_cast; linarith
  have hz : Function.Injective z := by
    intro j j' hjj
    apply E.injective
    have h1 := congrArg Real.exp hjj
    simp only [z, hzz] at h1
    obtain ⟨e1, e2, e3⟩ := mo17560_smooth_inj _ _ _ _ _ _ (by exact_mod_cast h1)
    exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))
  let e : Fin K × Fin K → Fin K × Fin K → ℤ := fun j i =>
    ((2 ^ ((i.1 : ℕ) * ((E j).1 : ℕ)) * 3 ^ ((i.1 : ℕ) * ((E j).2.1 : ℕ)) *
      5 ^ ((i.1 : ℕ) * ((E j).2.2 : ℕ)) * a ^ ((i.2 : ℕ) * ((E j).1 : ℕ)) *
      b ^ ((i.2 : ℕ) * ((E j).2.1 : ℕ)) * c ^ ((i.2 : ℕ) * ((E j).2.2 : ℕ)) : ℕ) : ℤ)
  have he : ∀ j i, Real.exp (z j * w i) = e j i := by
    intro j i
    have hzw : z j * w i =
        (((i.1 : ℕ) * ((E j).1 : ℕ) : ℕ) : ℝ) * Real.log 2 +
        (((i.1 : ℕ) * ((E j).2.1 : ℕ) : ℕ) : ℝ) * Real.log 3 +
        (((i.1 : ℕ) * ((E j).2.2 : ℕ) : ℕ) : ℝ) * Real.log 5 +
        (((i.2 : ℕ) * ((E j).1 : ℕ) : ℕ) : ℝ) * Real.log a +
        (((i.2 : ℕ) * ((E j).2.1 : ℕ) : ℕ) : ℝ) * Real.log b +
        (((i.2 : ℕ) * ((E j).2.2 : ℕ) : ℕ) : ℝ) * Real.log c := by
      simp only [z, zz, w]; rw [hla, hlb, hlc]; push_cast; ring
    rw [hzw]
    simp only [Real.exp_add, hexp _ _ (by norm_num : (0 : ℝ) < 2),
      hexp _ _ (by norm_num : (0 : ℝ) < 3), hexp _ _ (by norm_num : (0 : ℝ) < 5),
      hexp _ _ ha0, hexp _ _ hb0, hexp _ _ hc0]
    simp only [e]; push_cast; ring
  have hwb : ∀ i, |w i| ≤ K * u := by
    intro i
    have h1 : ((i.1 : ℕ) : ℝ) ≤ K := by exact_mod_cast i.1.isLt.le
    have h2 : ((i.2 : ℕ) : ℝ) ≤ K := by exact_mod_cast i.2.isLt.le
    calc |w i| ≤ |((i.1 : ℕ) : ℝ)| + |((i.2 : ℕ) : ℝ) * x| := abs_add_le _ _
      _ = (i.1 : ℕ) + ((i.2 : ℕ) : ℝ) * |x| := by rw [abs_mul, Nat.abs_cast, Nat.abs_cast]
      _ ≤ K + K * |x| := by gcongr
      _ = K * u := by rw [hu]; ring
  have hl2 : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := ⟨Real.log_nonneg (by norm_num),
    by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]⟩
  have hl3 : 0 ≤ Real.log 3 ∧ Real.log 3 ≤ 2 := ⟨Real.log_nonneg (by norm_num),
    by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]⟩
  have hl5 : 0 ≤ Real.log 5 ∧ Real.log 5 ≤ 4 := ⟨Real.log_nonneg (by norm_num),
    by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]⟩
  have hzb : ∀ j, |z j| ≤ 7 * H := by
    intro j
    have h1 : (((E j).1 : ℕ) : ℝ) ≤ H := by exact_mod_cast (E j).1.isLt.le
    have h2 : (((E j).2.1 : ℕ) : ℝ) ≤ H := by exact_mod_cast (E j).2.1.isLt.le
    have h3 : (((E j).2.2 : ℕ) : ℝ) ≤ H := by exact_mod_cast (E j).2.2.isLt.le
    have hnn : 0 ≤ z j := by
      simp only [z, zz]
      have := hl2.1; have := hl3.1; have := hl5.1
      positivity
    rw [abs_of_nonneg hnn]
    simp only [z, zz]
    have hH0 : (0 : ℝ) ≤ H := by positivity
    linarith [mul_le_mul h1 hl2.2 hl2.1 hH0, mul_le_mul h2 hl3.2 hl3.1 hH0,
      mul_le_mul h3 hl5.2 hl5.1 hH0]
  have hT : ∀ σ : Equiv.Perm (Fin K × Fin K), |∑ i, w i * z (σ i)| ≤ 7 * u * (P : ℝ) ^ 22 := by
    intro σ
    calc |∑ i, w i * z (σ i)| ≤ ∑ i, |w i * z (σ i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin K × Fin K, (K * u) * (7 * H) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hwb i) (hzb (σ i)) (abs_nonneg _) (by positivity)
      _ = 7 * u * (P : ℝ) ^ 22 := by
          rw [Finset.sum_const, Finset.card_univ, hcardι, nsmul_eq_mul, hK, hH]
          push_cast; ring
  refine mo17560_abstract w z hw hz e he (P ^ 23) (7 * u * (P : ℝ) ^ 22) ?_ hT ?_ ?_
  · rw [hcardι]
    have h1 : P ^ 12 ≤ P ^ 23 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : P ^ 12 * P ^ 12 = P * P ^ 23 := by ring
    rw [this]; nlinarith
  · rw [div_le_iff₀ (by positivity)]
    push_cast
    have : (P : ℝ) ^ 23 = (P : ℝ) ^ 22 * P := by ring
    rw [this]
    nlinarith [pow_pos hP0 22]
  · rw [hcardι]; exact mo17560_numeric u hu1 P hP3 hPu

theorem mathoverflow_17560.variants.with_5 {x : ℝ} (hx : ∃ m : ℕ, (2 : ℝ) ^ x = m)
    (hx' : ∃ m : ℕ, (3 : ℝ) ^ x = m) (hx'' : ∃ m : ℕ, (5 : ℝ) ^ x = m) : ∃ m : ℕ, x = m := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hx'
  obtain ⟨c, hc⟩ := hx''
  by_cases hirr : Irrational x
  · exact (mo17560_irrational hirr a b c ha hb hc).elim
  · rw [Irrational, not_not] at hirr
    obtain ⟨q, hq⟩ := hirr
    exact mo17560_rational q hq a ha

end OpenProofs.Mathoverflow17560
