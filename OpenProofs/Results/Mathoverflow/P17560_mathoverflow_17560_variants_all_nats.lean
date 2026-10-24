import FormalConjectures.Mathoverflow.«17560»

/-!
# `Mathoverflow17560.mathoverflow_17560.variants.all_nats`

Upstream: `Mathoverflow17560.mathoverflow_17560.variants.all_nats` (category textbook), `FormalConjectures/Mathoverflow/17560.lean` line 43.
Proof idea: `x ≥ 0` since `0 < 2 ^ x < 1` for `x < 0`. Suppose `x` is not a natural number and
let `k = ⌊x⌋₊ + 1 > x`. The `k`-th forward difference `Δ^k f (n)` of `f t = t ^ x` is an integer
(all `n ^ x` are). By the iterated mean value theorem (induction on `k` over a family of functions
with explicit derivatives) it equals `x (x - 1) ⋯ (x - k + 1) ξ ^ (x - k)` for some `ξ ≥ n`, which
is nonzero (no factor vanishes) and tends to `0` as `n → ∞` since `x - k < 0`. A nonzero integer
of absolute value `< 1` is impossible.
-/

open Mathoverflow17560

namespace OpenProofs.Mathoverflow17560

/-- Iterated mean value theorem for forward differences with step `1`. -/
theorem op17560_fwd_mvt (k : ℕ) : ∀ (F : ℕ → ℝ → ℝ),
    (∀ i, ∀ s : ℝ, 0 < s → HasDerivAt (F i) (F (i + 1) s) s) →
    ∀ t : ℝ, 0 < t → ∃ ξ : ℝ, t ≤ ξ ∧ ξ ≤ t + k ∧ (fwdDiff 1)^[k] (F 0) t = F k ξ := by
  induction k with
  | zero =>
    intro F _ t _
    exact ⟨t, le_rfl, by simp, by simp⟩
  | succ k ih =>
    intro F hF t ht
    set G : ℕ → ℝ → ℝ := fun i => fwdDiff 1 (F i) with hG
    have hGd : ∀ i, ∀ s : ℝ, 0 < s → HasDerivAt (G i) (G (i + 1) s) s := by
      intro i s hs
      have h1 : HasDerivAt (fun r => F i (r + 1)) (F (i + 1) (s + 1)) s :=
        (hF i (s + 1) (by linarith)).comp_add_const s 1
      show HasDerivAt (fun r => F i (r + 1) - F i r) (F (i + 1) (s + 1) - F (i + 1) s) s
      exact h1.sub (hF i s hs)
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ := ih G hGd t ht
    have hξpos : 0 < ξ := lt_of_lt_of_le ht hξ1
    obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope (F k) (F (k + 1))
      (show ξ < ξ + 1 by linarith)
      (fun y hy => (hF k y (by linarith [hy.1])).continuousAt.continuousWithinAt)
      (fun y hy => hF k y (by linarith [hy.1]))
    refine ⟨η, by linarith [hη.1], by push_cast; linarith [hη.2], ?_⟩
    rw [Function.iterate_succ_apply, hηeq]
    have : (fwdDiff 1)^[k] (fwdDiff 1 (F 0)) t = G k ξ := hξ
    rw [this]
    simp [hG, fwdDiff]

/-- Forward differences of a function that is integer-valued on the naturals stay so. -/
theorem op17560_fwd_int (k : ℕ) : ∀ (f : ℝ → ℝ), (∀ n : ℕ, ∃ z : ℤ, f n = z) →
    ∀ n : ℕ, ∃ z : ℤ, (fwdDiff 1)^[k] f n = z := by
  induction k with
  | zero => intro f hf n; simpa using hf n
  | succ k ih =>
    intro f hf
    rw [Function.iterate_succ]
    apply ih
    intro n
    obtain ⟨a, ha⟩ := hf (n + 1)
    obtain ⟨b, hb⟩ := hf n
    refine ⟨a - b, ?_⟩
    simp only [fwdDiff]
    push_cast at ha ⊢
    rw [ha, hb]

theorem mathoverflow_17560.variants.all_nats {x : ℝ} (hx : ∀ n : ℕ, ∃ m : ℕ, (n : ℝ) ^ x = m) :
    ∃ m : ℕ, x = m := by
  by_contra hne
  push Not at hne
  -- `x ≥ 0`
  have hx0 : 0 ≤ x := by
    by_contra hneg
    push Not at hneg
    obtain ⟨m, hm⟩ := hx 2
    have h1 : (2 : ℝ) ^ x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
    have h2 : (0 : ℝ) < 2 ^ x := Real.rpow_pos_of_pos (by norm_num) x
    push_cast at hm
    rw [hm] at h1 h2
    have h1' : m < 1 := by exact_mod_cast h1
    have h2' : 0 < m := by exact_mod_cast h2
    omega
  set k : ℕ := ⌊x⌋₊ + 1 with hk
  have hxk : x < k := by
    rw [hk]; push_cast; exact Nat.lt_floor_add_one x
  set c : ℝ := ∏ j ∈ Finset.range k, (x - j) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Finset.prod_ne_zero_iff]
    intro j _
    exact sub_ne_zero.mpr (hne j)
  set F : ℕ → ℝ → ℝ := fun i t => (∏ j ∈ Finset.range i, (x - j)) * t ^ (x - i) with hF
  have hFd : ∀ i, ∀ s : ℝ, 0 < s → HasDerivAt (F i) (F (i + 1) s) s := by
    intro i s hs
    have h := (Real.hasDerivAt_rpow_const (x := s) (p := x - i) (Or.inl hs.ne')).const_mul
      (∏ j ∈ Finset.range i, (x - j))
    show HasDerivAt (fun t => (∏ j ∈ Finset.range i, (x - j)) * t ^ (x - i))
      ((∏ j ∈ Finset.range (i + 1), (x - j)) * s ^ (x - ((i + 1 : ℕ) : ℝ))) s
    refine h.congr_deriv ?_
    rw [Finset.prod_range_succ]
    push_cast
    rw [show x - ((i : ℝ) + 1) = x - i - 1 by ring]
    ring
  have hF0 : F 0 = fun t => t ^ x := by
    funext t; simp [hF]
  have hint : ∀ n : ℕ, ∃ z : ℤ, (fwdDiff 1)^[k] (F 0) n = z := by
    apply op17560_fwd_int
    intro n
    obtain ⟨m, hm⟩ := hx n
    refine ⟨m, ?_⟩
    rw [hF0]; simp [hm]
  -- `n ^ (x - k) → 0`
  have htend : Filter.Tendsto (fun n : ℕ => |c| * (n : ℝ) ^ (x - k)) Filter.atTop (nhds 0) := by
    have h1 := (tendsto_rpow_neg_atTop (y := k - x) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul |c|
    simp only [mul_zero] at h2
    refine h2.congr ?_
    intro n
    simp
  have hev : ∀ᶠ n : ℕ in Filter.atTop, |c| * (n : ℝ) ^ (x - k) < 1 ∧ 1 ≤ n :=
    (htend.eventually (gt_mem_nhds (by norm_num))).and (Filter.eventually_ge_atTop 1)
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn2
  obtain ⟨ξ, hξ1, _, hξ⟩ := op17560_fwd_mvt k F hFd n hnpos
  obtain ⟨z, hz⟩ := hint n
  have hξpos : 0 < ξ := lt_of_lt_of_le hnpos hξ1
  have hFk : F k ξ = c * ξ ^ (x - k) := by simp [hF, hc]
  rw [hξ, hFk] at hz
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    simp only [Int.cast_zero] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact hc0 h
    · exact (Real.rpow_pos_of_pos hξpos _).ne' h
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast this
  have hle : ξ ^ (x - k) ≤ (n : ℝ) ^ (x - k) :=
    Real.rpow_le_rpow_of_nonpos hnpos hξ1 (by linarith)
  have habs : |(z : ℝ)| = |c| * ξ ^ (x - k) := by
    rw [← hz, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hξpos _)]
  have : |c| * ξ ^ (x - k) ≤ |c| * (n : ℝ) ^ (x - k) :=
    mul_le_mul_of_nonneg_left hle (abs_nonneg c)
  linarith

end OpenProofs.Mathoverflow17560
