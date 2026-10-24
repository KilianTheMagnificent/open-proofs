import FormalConjectures.ErdosProblems.«1055»

/-!
# `Erdos1055.exists_p`

Upstream: `Erdos1055.exists_p` (category textbook), `FormalConjectures/ErdosProblems/1055.lean` line 54.
Proof idea: unfold `IsOfClass` for class 1 and class `n + 1`. Classes are exclusive, and every
prime has a class (strong induction on `p`: the prime factors of `p + 1` are smaller than `p`
unless `p = 2`, and `p` gets class `1 +` the largest class among them). If `q ∣ p + 1` and `q`
is not 2 or 3, the class of `p` exceeds the class of `q`; so Dirichlet's theorem (a prime
`p > q` with `p ≡ -1 mod q`) gives primes of arbitrarily large class. A prime of class `n + 1`
has a prime factor of `p + 1` of class `n`, so descending from a large class reaches every class.
-/

open Erdos1055

namespace OpenProofs.Erdos1055

theorem cls1055_one (p : ℕ) : IsOfClass 1 p ↔ (p + 1).primeFactors ⊆ {2, 3} := by
  unfold IsOfClass PNat.caseStrongInductionOn
  rw [PNat.strongInductionOn]
  rfl

theorem cls1055_succ (n : ℕ+) (p : ℕ) : IsOfClass (n + 1) p ↔
    ((∀ (m : ℕ+), m ≤ n → ¬ IsOfClass m p) ∧
      (∀ r ∈ (p + 1).primeFactors, ∃ (m : ℕ+), m ≤ n ∧ IsOfClass m r) ∧
      (∃ r ∈ (p + 1).primeFactors, ∀ (m : ℕ+), m ≤ n → IsOfClass m r → m = n)) := by
  have h : IsOfClass (n + 1) p = ((∀ (m : ℕ+) (_ : m ≤ n), ¬ IsOfClass m p) ∧
      (∀ r ∈ (p + 1).primeFactors, ∃ (m : ℕ+) (_ : m ≤ n), IsOfClass m r) ∧
      (∃ r ∈ (p + 1).primeFactors, ∀ (m : ℕ+) (_ : m ≤ n), IsOfClass m r → m = n)) := by
    obtain ⟨k, hk⟩ := n
    obtain _ | k := k
    · exact absurd hk (lt_irrefl 0)
    conv_lhs => unfold IsOfClass PNat.caseStrongInductionOn; rw [PNat.strongInductionOn]
    rfl
  rw [h]
  simp only [exists_prop]

theorem cls1055_uniq {a b : ℕ+} {p : ℕ} (ha : IsOfClass a p) (hb : IsOfClass b p) : a = b := by
  have key : ∀ {a b : ℕ+}, IsOfClass a p → IsOfClass b p → ¬ a < b := by
    intro a b ha hb hab
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact absurd hab (not_lt_of_ge (one_le (a := a)))
    obtain ⟨n, rfl⟩ := PNat.exists_eq_succ_of_ne_one hb1
    exact ((cls1055_succ n p).1 hb).1 a (PNat.lt_add_one_iff.1 hab) ha
  rcases lt_trichotomy a b with h | h | h
  · exact absurd h (key ha hb)
  · exact h
  · exact absurd h (key hb ha)

theorem cls1055_factor {t s : ℕ+} {p q : ℕ} (hp : IsOfClass t p) (hq : q ∈ (p + 1).primeFactors)
    (hs : IsOfClass s q) : (t = 1 ∧ q ∈ ({2, 3} : Finset ℕ)) ∨ s < t := by
  by_cases ht : t = 1
  · subst ht
    exact Or.inl ⟨rfl, (cls1055_one p).1 hp hq⟩
  · obtain ⟨n, rfl⟩ := PNat.exists_eq_succ_of_ne_one ht
    obtain ⟨m, hm, hmq⟩ := ((cls1055_succ n p).1 hp).2.1 q hq
    have := cls1055_uniq hmq hs
    subst this
    exact Or.inr (PNat.lt_add_one_iff.2 hm)

theorem cls1055_descent {n : ℕ+} {p : ℕ} (hp : IsOfClass (n + 1) p) :
    ∃ q, q.Prime ∧ IsOfClass n q := by
  obtain ⟨-, h2, q, hq, h3⟩ := (cls1055_succ n p).1 hp
  obtain ⟨m, hm, hmq⟩ := h2 q hq
  exact ⟨q, Nat.prime_of_mem_primeFactors hq, h3 m hm hmq ▸ hmq⟩

theorem cls1055_total (p : ℕ) (hp : p.Prime) : ∃ t, IsOfClass t p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  by_cases h : (p + 1).primeFactors ⊆ {2, 3}
  · exact ⟨1, (cls1055_one p).2 h⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h (by rw [show 2 + 1 = 3 from rfl, Nat.prime_three.primeFactors]; decide)
  have hlt : ∀ q ∈ (p + 1).primeFactors, q < p := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqd := Nat.dvd_of_mem_primeFactors hq
    have hle := Nat.le_of_dvd (Nat.succ_pos p) hqd
    have hne1 : q ≠ p + 1 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      have h2 : 2 ∣ p + 1 := ⟨k + 1, by omega⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp).1 h2
      have := hp.two_le
      omega
    have hne2 : q ≠ p := by
      rintro rfl
      have : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).1 hqd
      exact hqp.one_lt.ne' (Nat.dvd_one.1 this)
    omega
  have hcls : ∀ q ∈ (p + 1).primeFactors, ∃ t, IsOfClass t q := fun q hq =>
    ih q (hlt q hq) (Nat.prime_of_mem_primeFactors hq)
  choose! c hc using hcls
  have hne : (p + 1).primeFactors.Nonempty := by
    rw [Nat.nonempty_primeFactors]
    have := hp.two_le
    omega
  obtain ⟨q₀, hq₀, hmax⟩ := Finset.exists_max_image _ c hne
  refine ⟨c q₀ + 1, (cls1055_succ (c q₀) p).2 ⟨?_, ?_, q₀, hq₀, ?_⟩⟩
  · intro m hm hmp
    rcases cls1055_factor hmp hq₀ (hc q₀ hq₀) with ⟨rfl, -⟩ | hlt'
    · exact h ((cls1055_one p).1 hmp)
    · exact absurd hm (not_le_of_gt hlt')
  · intro q hq
    exact ⟨c q, hmax q hq, hc q hq⟩
  · intro m _ hm
    exact cls1055_uniq hm (hc q₀ hq₀)

theorem cls1055_unbounded (r : ℕ+) : ∃ p, p.Prime ∧ 5 ≤ p ∧ ∃ t, r ≤ t ∧ IsOfClass t p := by
  induction r using PNat.recOn with
  | one =>
    obtain ⟨t, ht⟩ := cls1055_total 5 (by norm_num)
    exact ⟨5, by norm_num, le_rfl, t, one_le (a := t), ht⟩
  | succ r ih =>
    obtain ⟨q, hq, hq5, t, hrt, ht⟩ := ih
    have hcop : (q - 1).Coprime q := by
      rw [Nat.coprime_self_sub_left hq.one_lt.le]
      exact Nat.coprime_one_left q
    obtain ⟨p, hpq, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq q hq.ne_zero hcop
    have hdvd : q ∣ p + 1 := by
      have h1 : p + 1 ≡ q - 1 + 1 [MOD q] := hmod.add_right 1
      rw [Nat.sub_add_cancel hq.one_lt.le] at h1
      exact (Nat.modEq_zero_iff_dvd).1 (h1.trans (Nat.modEq_zero_iff_dvd.2 (dvd_refl q)))
    have hmem : q ∈ (p + 1).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.succ_ne_zero p⟩
    obtain ⟨t', ht'⟩ := cls1055_total p hp
    refine ⟨p, hp, by omega, t', ?_, ht'⟩
    rcases cls1055_factor ht' hmem ht with ⟨-, h23⟩ | hlt
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h23
      omega
    · exact PNat.add_one_le_iff.2 (lt_of_le_of_lt hrt hlt)

theorem cls1055_down (t : ℕ+) (ht : ∃ p, p.Prime ∧ IsOfClass t p) :
    ∀ r ≤ t, ∃ p, p.Prime ∧ IsOfClass r p := by
  induction t using PNat.recOn with
  | one =>
    intro r hr
    rw [le_one_iff_eq_one.1 hr]
    exact ht
  | succ n ih =>
    intro r hr
    rcases eq_or_lt_of_le hr with rfl | hlt
    · exact ht
    · obtain ⟨p, -, hp⟩ := ht
      exact ih (cls1055_descent hp) r (PNat.lt_add_one_iff.1 hlt)

theorem exists_p (r : ℕ+) : ∃ p, p.Prime ∧ IsOfClass r p := by
  obtain ⟨p, hp, -, t, hrt, ht⟩ := cls1055_unbounded r
  exact cls1055_down t ⟨p, hp, ht⟩ r hrt

end OpenProofs.Erdos1055
