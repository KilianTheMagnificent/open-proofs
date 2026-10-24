import FormalConjectures.ErdosProblems.«945»

/-!
# `Erdos945.erdos_945.variants.equivalence`

Upstream: `Erdos945.erdos_945.variants.equivalence` (category textbook), `FormalConjectures/ErdosProblems/945.lean` line 74.
Proof idea: (→) If `F y ≤ (log y)^M` eventually, take `C = M + 1`. If `[x, x + (log x)^C]`
had no two integers with equal `τ`, the `⌊(log x)^C⌋` integers starting at `⌈x⌉` would give
`(log x)^(M+1) - 1 < F (x + (log x)^C) ≤ (2 log x)^M`, false for large `x` (using
`(log x)^C ≤ x`). (←) With the constant `C` and threshold `X0`, any block `(n, n+k]` below `x`
on which `τ` is injective has `k < 1 + X0 + (log x)^C` (otherwise it contains
`[y, y + (log y)^C]` for `y = max (n+1) X0`), so `F x ≤ (log x)^(C+1)` eventually.
-/

open Filter Real
open Erdos945

namespace OpenProofs.Erdos945

lemma erdos945Equiv_le_F {y : ℝ} {n k : ℕ} (h : (n : ℝ) + k ≤ y)
    (hinj : (Set.Ioc n (n + k)).InjOn τ) : k ≤ F y := by
  unfold F
  apply le_csSup
  · refine ⟨⌊y⌋₊, ?_⟩
    rintro k' ⟨n', hn', -⟩
    apply Nat.le_floor
    have : (0:ℝ) ≤ n' := Nat.cast_nonneg _
    linarith
  · exact ⟨n, h, hinj⟩

lemma erdos945Equiv_F_le {x B : ℝ} (hB : 0 ≤ B)
    (h : ∀ n k : ℕ, (n : ℝ) + k ≤ x → (Set.Ioc n (n + k)).InjOn τ → (k : ℝ) ≤ B) :
    (F x : ℝ) ≤ B := by
  have : F x ≤ ⌊B⌋₊ := by
    unfold F
    apply csSup_le'
    rintro k ⟨n, hn, hinj⟩
    exact Nat.le_floor (h n k hn hinj)
  calc (F x : ℝ) ≤ ⌊B⌋₊ := by exact_mod_cast this
    _ ≤ B := Nat.floor_le hB

theorem erdos_945.variants.equivalence : Erdos945Prop ↔ Erdos945Constant := by
  constructor
  · rintro ⟨O, hO, hF⟩
    obtain ⟨c, hc⟩ := hO.bound
    set M := max c 0 with hM
    have hM0 : 0 ≤ M := le_max_right _ _
    have hFM : ∀ᶠ y in atTop, (F y : ℝ) ≤ log y ^ M := by
      filter_upwards [hF, hc, Real.tendsto_log_atTop.eventually_ge_atTop 1] with y h1 h2 h3
      simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs] at h2
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le h3 ?_)
      exact (le_abs_self _).trans (h2.trans (le_max_left _ _))
    obtain ⟨Y, hY⟩ := eventually_atTop.1 hFM
    refine ⟨M + 1, by linarith, ?_⟩
    have hLo := (isLittleO_log_rpow_rpow_atTop (M + 1) one_pos).bound one_pos
    filter_upwards [hLo, eventually_ge_atTop Y, eventually_ge_atTop 2,
      Real.tendsto_log_atTop.eventually_ge_atTop ((2:ℝ) ^ M + 1)] with x hLx hxY hx2 hlog
    have hx0 : 0 < x := by linarith
    have ht1 : 1 ≤ log x := by
      have : (1:ℝ) ≤ 2 ^ M := Real.one_le_rpow (by norm_num) hM0
      linarith
    have hL0 : 0 ≤ log x ^ (M + 1) := Real.rpow_nonneg (by linarith) _
    have hLx' : log x ^ (M + 1) ≤ x := by
      simp only [Real.norm_eq_abs, Real.rpow_one, one_mul] at hLx
      rw [abs_of_nonneg hL0, abs_of_pos hx0] at hLx
      exact hLx
    set t := log x with ht
    set L := t ^ (M + 1) with hL
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ : ∃ n, ⌈x⌉₊ = n + 1 :=
      ⟨⌈x⌉₊ - 1, by have := Nat.ceil_pos.2 hx0; omega⟩
    have hn' : ((n:ℝ) + 1) = ⌈x⌉₊ := by rw [hn]; push_cast; ring
    have hxle : x ≤ n + 1 := hn' ▸ Nat.le_ceil x
    have hlt : (n:ℝ) + 1 < x + 1 := hn' ▸ Nat.ceil_lt_add_one hx0.le
    set k := ⌊L⌋₊ with hk
    have hkL : (k:ℝ) ≤ L := Nat.floor_le hL0
    have hLk : L < k + 1 := Nat.lt_floor_add_one L
    have hmem : ∀ i ∈ Set.Ioc n (n + k), (i:ℝ) ∈ Set.Icc x (x + L) := by
      rintro i ⟨hi1, hi2⟩
      have h1 : (n:ℝ) + 1 ≤ i := by exact_mod_cast hi1
      have h2 : (i:ℝ) ≤ n + k := by exact_mod_cast hi2
      constructor <;> linarith
    have hinj : (Set.Ioc n (n + k)).InjOn τ := by
      intro i hi j hj hij
      by_contra hne
      exact hcon i j hne (hmem i hi) (hmem j hj) hij
    have hkF := erdos945Equiv_le_F (y := x + L) (by linarith) hinj
    have hFb := hY (x + L) (by linarith)
    have hlog2 : log (x + L) ≤ 2 * t := by
      have : x + L ≤ x * x := by nlinarith
      calc log (x + L) ≤ log (x * x) := Real.log_le_log (by linarith) this
        _ = 2 * t := by rw [Real.log_mul hx0.ne' hx0.ne']; ring
    have hlog0 : 0 ≤ log (x + L) := Real.log_nonneg (by linarith)
    have h3 : log (x + L) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow hlog0 hlog2 hM0
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h3
    have hu : 1 ≤ t ^ M := Real.one_le_rpow ht1 hM0
    have hLeq : L = t ^ M * t := Real.rpow_add_one (by linarith) M
    have hkb : (k:ℝ) ≤ 2 ^ M * t ^ M := by
      calc (k:ℝ) ≤ F (x + L) := by exact_mod_cast hkF
        _ ≤ _ := hFb
        _ ≤ _ := h3
    nlinarith [mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ t ^ M)]
  · rintro ⟨C, hC, hev⟩
    obtain ⟨X, hX⟩ := eventually_atTop.1 hev
    set X0 := max X 0 with hX0
    have hX00 : 0 ≤ X0 := le_max_right _ _
    refine ⟨fun _ => C + 1, ?_, ?_⟩
    · exact Asymptotics.isBigO_const_one ℝ (C + 1) atTop
    · filter_upwards [eventually_ge_atTop X0,
        Real.tendsto_log_atTop.eventually_ge_atTop (2 + X0)] with x hxX hlog
      have ht1 : 1 ≤ log x := by linarith
      have hu : 1 ≤ log x ^ C := Real.one_le_rpow ht1 hC.le
      have hB : 1 + X0 + log x ^ C ≤ log x ^ (C + 1) := by
        rw [Real.rpow_add_one (by linarith)]
        nlinarith
      refine (erdos945Equiv_F_le (B := 1 + X0 + log x ^ C) (by linarith) ?_).trans hB
      intro n k hnk hinj
      by_contra hk
      push Not at hk
      set y : ℝ := max ((n:ℝ) + 1) X0 with hy
      have hyX : X ≤ y := (le_max_left X 0).trans (le_max_right _ _)
      obtain ⟨a, b, hab, ha, hb, hτ⟩ := hX y hyX
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have hy1 : (n:ℝ) + 1 ≤ y := le_max_left _ _
      have hyle : y ≤ n + 1 + X0 := max_le (by linarith) (by linarith)
      have hyx : y ≤ x := max_le (by linarith) hxX
      have hlogy : log y ^ C ≤ log x ^ C :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hyx) hC.le
      have hmem : ∀ c : ℕ, (c:ℝ) ∈ Set.Icc y (y + log y ^ C) → c ∈ Set.Ioc n (n + k) := by
        rintro c ⟨hc1, hc2⟩
        constructor
        · have : (n:ℝ) < c := by linarith
          exact_mod_cast this
        · have : (c:ℝ) ≤ n + k := by linarith
          exact_mod_cast this
      exact hab (hinj (hmem a ha) (hmem b hb) hτ)

end OpenProofs.Erdos945
