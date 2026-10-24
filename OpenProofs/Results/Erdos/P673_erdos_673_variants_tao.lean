import FormalConjectures.ErdosProblems.«673»

/-!
# `Erdos673.erdos_673.variants.tao`

Upstream: `Erdos673.erdos_673.variants.tao` (category textbook), `FormalConjectures/ErdosProblems/673.lean` line 77.
Proof idea: write `d_i = Nat.nth (· ∣ n) i` for the `i`-th divisor (`i < τ(n)`). Every term
`d_i / d_{i+1}` of `G n` lies in `[0, 1]`, so `G n ≤ τ(n) - 1 ≤ τ(n)`. For the lower bound,
each divisor `e` of `n / m` gives the divisor `e * m` of `n`, at index `j = Nat.count (· ∣ n) (e * m) ≥ 1`;
the previous divisor `d_{j-1}` is at least `e` (because `e < e * m` divides `n`), so the term at
index `j - 1` is at least `e / (e * m) = 1 / m`. The map `e ↦ j - 1` is injective, and all other
terms are nonnegative, hence `G n ≥ τ(n / m) / m`.
-/

open Filter Asymptotics Real
open Erdos673

namespace OpenProofs.Erdos673

theorem erdos_673.variants.tao (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n ∧ G n ≤ n.divisors.card := by
  classical
  set p : ℕ → Prop := (· ∣ n) with hp
  have hfin : (Set.ofPred p).Finite := by
    apply (Set.finite_Iic n).subset
    intro x hx
    exact Nat.le_of_dvd hn hx
  have hcard : hfin.toFinset.card = n.divisors.card := by
    congr 1
    ext x
    simp [Set.Finite.mem_toFinset, Nat.mem_divisors, hn.ne', hp]
  set k := n.divisors.card with hk
  have hlt : ∀ {i j : ℕ}, i < j → j < k → Nat.nth p i < Nat.nth p j := by
    intro i j hij hj
    exact Nat.nth_lt_nth' hij (fun hf => by rwa [hcard])
  have hle : ∀ {i j : ℕ}, i ≤ j → j < k → Nat.nth p i ≤ Nat.nth p j := by
    intro i j hij hj
    exact Nat.nth_le_nth' hij (fun hf => by rwa [hcard])
  have hcnt : ∀ {d : ℕ}, p d → Nat.count p d < k := by
    intro d hd
    rw [← hcard]
    exact Nat.count_lt_card hfin hd
  unfold G
  rw [Fin.sum_univ_eq_sum_range (fun i => (Nat.nth p i : ℝ) / (Nat.nth p (i + 1) : ℝ))]
  have hnonneg : ∀ i, 0 ≤ (Nat.nth p i : ℝ) / (Nat.nth p (i + 1) : ℝ) := fun i => by positivity
  constructor
  · have hm0 : 0 < m := by omega
    have hp1 : p 1 := one_dvd n
    set D := (n / m).divisors with hD
    have hemd : ∀ e ∈ D, p (e * m) := by
      intro e he
      have he' := (Nat.mem_divisors.mp he).1
      have : e * m ∣ n / m * m := Nat.mul_dvd_mul_right he' m
      rwa [Nat.div_mul_cancel hmn] at this
    have hepos : ∀ e ∈ D, 0 < e := fun e he => Nat.pos_of_mem_divisors he
    have hc1 : ∀ e ∈ D, 1 ≤ Nat.count p (e * m) := by
      intro e he
      have h1 : 1 < e * m := by nlinarith [hepos e he]
      have := Nat.count_strict_mono hp1 h1
      omega
    set g : ℕ → ℕ := fun e => Nat.count p (e * m) - 1 with hg
    have hgmem : ∀ e ∈ D, g e ∈ Finset.range (k - 1) := by
      intro e he
      rw [Finset.mem_range]
      have := hcnt (hemd e he)
      have := hc1 e he
      simp only [hg]
      omega
    have hginj : ∀ x ∈ D, ∀ y ∈ D, g x = g y → x = y := by
      intro x hx y hy hxy
      have h1 := hc1 x hx
      have h2 := hc1 y hy
      have : Nat.count p (x * m) = Nat.count p (y * m) := by simp only [hg] at hxy; omega
      have := Nat.count_injective (hemd x hx) (hemd y hy) this
      exact Nat.eq_of_mul_eq_mul_right hm0 this
    have hterm : ∀ e ∈ D, (1 : ℝ) / m ≤ (Nat.nth p (g e) : ℝ) / (Nat.nth p (g e + 1) : ℝ) := by
      intro e he
      have hc := hc1 e he
      have hge1 : g e + 1 = Nat.count p (e * m) := by simp only [hg]; omega
      rw [hge1, Nat.nth_count (hemd e he)]
      have hpe : p e := (Nat.dvd_trans (Nat.mem_divisors.mp he).1 (Nat.div_dvd_of_dvd hmn))
      have hem : e < e * m := by nlinarith [hepos e he]
      have hce : Nat.count p e ≤ g e := by
        have := Nat.count_strict_mono hpe hem
        simp only [hg]; omega
      have hgk : g e < k := by have := hcnt (hemd e he); simp only [hg]; omega
      have hle' : e ≤ Nat.nth p (g e) := by
        have := hle hce hgk
        rwa [Nat.nth_count hpe] at this
      have hepos' : (0 : ℝ) < e := by exact_mod_cast hepos e he
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
      calc (1 : ℝ) / m = (e : ℝ) / ((e * m : ℕ) : ℝ) := by
              push_cast; field_simp
        _ ≤ (Nat.nth p (g e) : ℝ) / ((e * m : ℕ) : ℝ) := by
              apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
              exact_mod_cast hle'
    calc ((n / m).divisors.card : ℝ) / m = ∑ e ∈ D, (1 : ℝ) / m := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ e ∈ D, (Nat.nth p (g e) : ℝ) / (Nat.nth p (g e + 1) : ℝ) :=
          Finset.sum_le_sum hterm
      _ = ∑ i ∈ D.image g, (Nat.nth p i : ℝ) / (Nat.nth p (i + 1) : ℝ) :=
          (Finset.sum_image (f := fun i => (Nat.nth p i : ℝ) / (Nat.nth p (i + 1) : ℝ))
            hginj).symm
      _ ≤ ∑ i ∈ Finset.range (k - 1), (Nat.nth p i : ℝ) / (Nat.nth p (i + 1) : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
            exact hgmem e he
          · intro i _ _
            exact hnonneg i
  · calc ∑ i ∈ Finset.range (k - 1), (Nat.nth p i : ℝ) / (Nat.nth p (i + 1) : ℝ)
          ≤ ∑ i ∈ Finset.range (k - 1), (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_range] at hi
            apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
            exact_mod_cast hle (Nat.le_succ i) (by omega)
      _ ≤ k := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
            exact_mod_cast Nat.sub_le k 1

end OpenProofs.Erdos673
