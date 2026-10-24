import FormalConjectures.ErdosProblems.«44»

/-!
# `Erdos44.sidon_set_lower_bound`

Upstream: `Erdos44.sidon_set_lower_bound` (category textbook), `FormalConjectures/ErdosProblems/44.lean` line 129.
Proof idea: the Erdős–Turán construction. For an odd prime `p` and `K ≤ p`, the numbers
`2pk + (k² mod p) + 1` (`k < K`) form a Sidon set: a coincidence of sums forces equal sums
`k₁ + k₂` (the residues add up to less than `2p`) and equal sums of squares modulo `p`, hence equal
products modulo `p` (as `p` is odd), and so the same unordered pair. For `N ≥ 16` let
`t = ⌊√N⌋ / 2` and take a Bertrand prime `t < p ≤ 2t` (in fact `p < 2t`) and `K = t + 1`; then
the set lies in `{1, …, N}` and `N ≤ 4K²`. For `N < 16` the sets `{1}` and `{1, 2}` suffice.
-/

open Function Set Finset
open Erdos44

namespace OpenProofs.Erdos44

/-- Modulo an odd prime, the sum and the sum of squares determine an unordered pair. -/
theorem erdosTuran_pair_eq {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {a b c d : ℕ}
    (ha : a < p) (hc : c < p) (hd : d < p)
    (hs : a + b = c + d) (hq : a ^ 2 % p + b ^ 2 % p = c ^ 2 % p + d ^ 2 % p) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have := Fact.mk hp
  have hs' : (a : ZMod p) + b = c + d := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hs
  have hq' : (a : ZMod p) ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hq
    push_cast [ZMod.natCast_mod] at this
    exact this
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hprod : (a : ZMod p) * b = c * d := by
    have h0 : (2 : ZMod p) * ((a : ZMod p) * b - c * d) = 0 := by
      linear_combination (↑a + ↑b + ↑c + ↑d) * hs' - hq'
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h h2
    · exact sub_eq_zero.mp h
  have hfac : ((a : ZMod p) - c) * ((a : ZMod p) - d) = 0 := by
    linear_combination (a : ZMod p) * hs' - hprod
  rcases mul_eq_zero.mp hfac with h | h
  · have h' := (ZMod.natCast_eq_natCast_iff' a c p).mp (sub_eq_zero.mp h)
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at h'
    left
    omega
  · have h' := (ZMod.natCast_eq_natCast_iff' a d p).mp (sub_eq_zero.mp h)
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd] at h'
    right
    omega

/-- `(2p·x + y) / (2p) = x` for `y < 2p`. -/
theorem erdosTuran_div {p x y : ℕ} (hp : 0 < p) (hy : y < 2 * p) :
    (2 * p * x + y) / (2 * p) = x := by
  rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hy, Nat.add_zero]

/-- The Erdős–Turán set `{2pk + (k² mod p) + 1 : k < K}` is a Sidon set. -/
theorem erdosTuran_isSidon {p K : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hK : K ≤ p) :
    IsSidon (((Finset.range K).image fun k => 2 * p * k + k ^ 2 % p + 1 : Finset ℕ) : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨a, ha, rfl⟩ := hi₁
  obtain ⟨c, hc, rfl⟩ := hj₁
  obtain ⟨b, hb, rfl⟩ := hi₂
  obtain ⟨d, hd, rfl⟩ := hj₂
  have hp0 : 0 < p := hp.pos
  have hra := Nat.mod_lt (a ^ 2) hp0
  have hrb := Nat.mod_lt (b ^ 2) hp0
  have hrc := Nat.mod_lt (c ^ 2) hp0
  have hrd := Nat.mod_lt (d ^ 2) hp0
  have key : 2 * p * (a + b) + (a ^ 2 % p + b ^ 2 % p)
      = 2 * p * (c + d) + (c ^ 2 % p + d ^ 2 % p) := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have hsum : a + b = c + d := by
    have e1 := erdosTuran_div (x := a + b) hp0 (by omega : a ^ 2 % p + b ^ 2 % p < 2 * p)
    have e2 := erdosTuran_div (x := c + d) hp0 (by omega : c ^ 2 % p + d ^ 2 % p < 2 * p)
    rw [key] at e1
    omega
  have hq : a ^ 2 % p + b ^ 2 % p = c ^ 2 % p + d ^ 2 % p := by
    rw [hsum] at key
    omega
  rcases erdosTuran_pair_eq hp hp3 (by omega) (by omega) (by omega) hsum hq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Choice of parameters for `N ≥ 16`, via Bertrand's postulate. -/
theorem erdosTuran_params {N : ℕ} (hN : 16 ≤ N) :
    ∃ p K : ℕ, p.Prime ∧ 3 ≤ p ∧ K ≤ p ∧ N ≤ 4 * K ^ 2 ∧ 2 * p * K ≤ N + p := by
  set s := Nat.sqrt N with hsdef
  have hs1 : s * s ≤ N := Nat.sqrt_le N
  have hs2 : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hs4 : 4 ≤ s := Nat.le_sqrt.mpr (by omega)
  set t := s / 2 with htdef
  have ht2 : 2 ≤ t := by omega
  have hts : 2 * t ≤ s := by omega
  have hts' : s ≤ 2 * t + 1 := by omega
  obtain ⟨p, hp, htp, hp2t⟩ := Nat.exists_prime_lt_and_le_two_mul t (by omega)
  have hpne : p ≠ 2 * t := by
    intro hpe
    have h2 : 2 ∣ p := ⟨t, hpe⟩
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  refine ⟨p, t + 1, hp, by omega, by omega, ?_, ?_⟩
  · have : s + 1 ≤ 2 * (t + 1) := by omega
    nlinarith
  · have hp' : p + 1 ≤ 2 * t := by omega
    nlinarith

/-- The set `{1, 2}` is a Sidon set. -/
theorem erdosTuran_isSidon_one_two : IsSidon (({1, 2} : Finset ℕ) : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  omega

theorem sidon_set_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ Real.sqrt N / 2 ≤ A.card := by
  suffices h : ∃ A ⊆ Finset.Icc 1 N, IsSidon (A : Set ℕ) ∧ N ≤ 4 * A.card ^ 2 by
    obtain ⟨A, hA, hS, hc⟩ := h
    refine ⟨A, hA, hS, ?_⟩
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), Real.sqrt_le_left (by positivity)]
    have : (N : ℝ) ≤ 4 * (A.card : ℝ) ^ 2 := by exact_mod_cast hc
    nlinarith
  rcases Nat.lt_or_ge N 4 with h4 | h4
  · refine ⟨{1}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ _
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
      subst hi₁ hj₁ hi₂ hj₂
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [Finset.card_singleton]
      omega
  rcases Nat.lt_or_ge N 16 with h16 | h16
  · refine ⟨{1, 2}, ?_, erdosTuran_isSidon_one_two, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]
      omega
    · rw [Finset.card_pair (by norm_num)]
      omega
  obtain ⟨p, K, hp, hp3, hKp, hNK, hpK⟩ := erdosTuran_params h16
  refine ⟨(Finset.range K).image fun k => 2 * p * k + k ^ 2 % p + 1, ?_,
    erdosTuran_isSidon hp hp3 hKp, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hr := Nat.mod_lt (k ^ 2) hp.pos
    have hmul : 2 * p * (k + 1) ≤ 2 * p * K := Nat.mul_le_mul_left _ hk
    rw [Nat.mul_add, Nat.mul_one] at hmul
    simp only [Finset.mem_Icc]
    omega
  · rw [Finset.card_image_of_injective]
    · simpa using hNK
    · intro a b hab
      have hp0 : 0 < p := hp.pos
      have e1 := erdosTuran_div (x := a) hp0 (by
        have := Nat.mod_lt (a ^ 2) hp0; omega : a ^ 2 % p + 1 < 2 * p)
      have e2 := erdosTuran_div (x := b) hp0 (by
        have := Nat.mod_lt (b ^ 2) hp0; omega : b ^ 2 % p + 1 < 2 * p)
      simp only at hab
      rw [← Nat.add_assoc, hab, Nat.add_assoc] at e1
      omega

end OpenProofs.Erdos44
