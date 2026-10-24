import FormalConjectures.ErdosProblems.«358»

/-!
# `Erdos358.f_id`

Upstream: `Erdos358.f_id` (category textbook), `FormalConjectures/ErdosProblems/358.lean` line 66.
Proof idea: for `n = 0` the set of representations is infinite (every `u > v` gives an empty
sum), so `Nat.card` is `0`, matching the empty divisor set. For `n > 0`, a representation
`u ≤ v` satisfies `2n = (v + 1 - u)(u + v)` with factors of opposite parity, so exactly one of
them is an odd divisor `d` of `n`. Conversely each odd divisor `d` with `e = 2n/d` gives the
representation `u = (max d e - min d e + 1)/2`, `v = (d + e - 1)/2`. This map is injective on odd
divisors and its image is the representation set, so both sides have the same cardinality.
-/

open Filter Finset
open Erdos358

namespace OpenProofs.Erdos358

theorem sum_Icc_id_two_mul_aux (u t : ℕ) :
    2 * ∑ i ∈ Icc u (u + t), i = (t + 1) * (2 * u + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← Nat.add_assoc, Finset.sum_Icc_succ_top (by omega), Nat.mul_add, ih]
    ring

theorem sum_Icc_id_two_mul' {u v : ℕ} (h : u ≤ v) :
    2 * ∑ i ∈ Icc u v, i = (v + 1 - u) * (u + v) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [sum_Icc_id_two_mul_aux]
  have : u + t + 1 - u = t + 1 := by omega
  rw [this]; ring

theorem f_id : f id = fun n ↦ #{d ∈ n.divisors | Odd d} := by
  classical
  funext n
  show Nat.card (intervalRepresentations id n) = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hinf : (intervalRepresentations id 0).Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + 2, 1)) ?_ ?_
      · intro x y h
        simpa using h
      · intro k
        simp only [intervalRepresentations, Set.mem_ofPred_eq]
        refine ⟨by omega, by omega, ?_⟩
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    simp only [Nat.divisors_zero, Finset.filter_empty, Finset.card_empty]
    exact @Nat.card_eq_zero_of_infinite _ hinf.to_subtype
  · set D : Finset ℕ := {d ∈ n.divisors | Odd d} with hD
    set φ : ℕ → ℕ × ℕ := fun d =>
      ((max d (2 * n / d) - min d (2 * n / d) + 1) / 2, (d + 2 * n / d - 1) / 2) with hφ
    have key : ∀ d ∈ D, ∃ a c, d = 2 * a + 1 ∧ 2 * n / d = 2 * c ∧ n = (2 * a + 1) * c ∧ 0 < c := by
      intro d hd
      rw [hD, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨⟨c, hc⟩, -⟩, ⟨a, ha⟩⟩ := hd
      refine ⟨a, c, ha, ?_, by rw [hc, ha], ?_⟩
      · rw [hc, show 2 * (d * c) = d * (2 * c) by ring, Nat.mul_div_cancel_left _ (by omega)]
      · rcases Nat.eq_zero_or_pos c with h | h
        · rw [h, Nat.mul_zero] at hc; omega
        · exact h
    have hφd : ∀ d ∈ D, ∃ a c, n = (2 * a + 1) * c ∧ 0 < c ∧ d = 2 * a + 1 ∧
        (φ d).2 = a + c ∧ (a < c → (φ d).1 = c - a) ∧ (c ≤ a → (φ d).1 = a - c + 1) := by
      intro d hd
      obtain ⟨a, c, rfl, he, hn', hc⟩ := key d hd
      refine ⟨a, c, hn', hc, rfl, ?_, ?_, ?_⟩
      · simp only [hφ, he]; omega
      · intro h; simp only [hφ, he]; omega
      · intro h; simp only [hφ, he]; omega
    have hinj : Set.InjOn φ D := by
      intro d hd d' hd' h
      obtain ⟨a, c, -, -, rfl, h2, h3, h4⟩ := hφd d hd
      obtain ⟨a', c', -, -, rfl, h2', h3', h4'⟩ := hφd d' hd'
      rw [h] at h2 h3 h4
      rcases lt_or_ge a c with h5 | h5 <;> rcases lt_or_ge a' c' with h6 | h6
      · have := h3 h5; have := h3' h6; omega
      · have := h3 h5; have := h4' h6; omega
      · have := h4 h5; have := h3' h6; omega
      · have := h4 h5; have := h4' h6; omega
    have hS : intervalRepresentations id n = ↑(D.image φ) := by
      ext ⟨u, v⟩
      simp only [intervalRepresentations, Set.mem_ofPred_eq, id, Finset.coe_image,
        Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨hu, hv, hsum⟩
        have huv : u ≤ v := by
          by_contra hc
          rw [Finset.Icc_eq_empty hc, Finset.sum_empty] at hsum
          omega
        have h2 := sum_Icc_id_two_mul' huv
        rw [← hsum] at h2
        rcases Nat.even_or_odd (v + 1 - u) with ⟨b, hb⟩ | ⟨a, ha⟩
        · refine ⟨u + v, ?_, ?_⟩
          · rw [hD, Finset.mem_filter, Nat.mem_divisors]
            refine ⟨⟨⟨b, ?_⟩, hn.ne'⟩, ⟨v - b, by omega⟩⟩
            rw [hb] at h2
            have : 2 * n = 2 * ((u + v) * b) := by rw [h2]; ring
            omega
          · have he : 2 * n / (u + v) = b + b := by
              rw [h2, hb, Nat.mul_div_cancel _ (by omega)]
            simp only [hφ, he]
            ext <;> simp only <;> omega
        · refine ⟨v + 1 - u, ?_, ?_⟩
          · rw [hD, Finset.mem_filter, Nat.mem_divisors]
            refine ⟨⟨⟨v - a, ?_⟩, hn.ne'⟩, ⟨a, ha⟩⟩
            have h3 : u + v = 2 * (v - a) := by omega
            rw [h3] at h2
            have : 2 * n = 2 * ((v + 1 - u) * (v - a)) := by rw [h2]; ring
            omega
          · have he : 2 * n / (v + 1 - u) = u + v := by
              rw [h2, Nat.mul_div_cancel_left _ (by omega)]
            simp only [hφ, he]
            ext <;> simp only <;> omega
      · rintro ⟨d, hd, hdu⟩
        obtain ⟨a, c, hn', hc, -, h2, h3, h4⟩ := hφd d hd
        rw [hdu] at h2 h3 h4
        simp only at h2 h3 h4
        rcases lt_or_ge a c with h5 | h5
        · have h6 := h3 h5
          subst h2 h6
          refine ⟨by omega, by omega, ?_⟩
          have h7 := sum_Icc_id_two_mul' (show c - a ≤ a + c by omega)
          rw [show a + c + 1 - (c - a) = 2 * a + 1 by omega,
            show c - a + (a + c) = 2 * c by omega] at h7
          have : 2 * n = 2 * ((2 * a + 1) * c) := by rw [hn']
          have : (2 * a + 1) * (2 * c) = 2 * ((2 * a + 1) * c) := by ring
          omega
        · have h6 := h4 h5
          subst h2 h6
          refine ⟨by omega, by omega, ?_⟩
          have h7 := sum_Icc_id_two_mul' (show a - c + 1 ≤ a + c by omega)
          rw [show a + c + 1 - (a - c + 1) = 2 * c by omega,
            show a - c + 1 + (a + c) = 2 * a + 1 by omega] at h7
          have : 2 * n = 2 * ((2 * a + 1) * c) := by rw [hn']
          have : 2 * c * (2 * a + 1) = 2 * ((2 * a + 1) * c) := by ring
          omega
    rw [hS, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

end OpenProofs.Erdos358
