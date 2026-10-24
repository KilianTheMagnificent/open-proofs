import FormalConjectures.Wikipedia.LeinsterGroup

/-!
# `LeinsterGroup.cyclic_of_perfect_is_leinster`

Upstream: `LeinsterGroup.cyclic_of_perfect_is_leinster` (category API), `FormalConjectures/Wikipedia/LeinsterGroup.lean` line 74.
Proof idea: in a finite cyclic group of order `n` every subgroup is normal, and
`H ↦ Nat.card H` is a bijection from subgroups onto the divisors of `n`: the cardinality divides
`n` (Lagrange); a subgroup of order `d` is exactly the set `{a | a ^ d = 1}` because that set has
at most `d` elements (`IsCyclic.card_pow_eq_one_le`), giving injectivity; and `zpowers (g ^ (n / d))`
for a generator `g` has order `d`, giving surjectivity. So the sum of the orders of the normal
subgroups is `σ(n) = 2n` for perfect `n`.
-/

open LeinsterGroup

namespace OpenProofs.LeinsterGroup

theorem cyclicLeinster_subgroup_eq_of_card_eq {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (H K : Subgroup G) (h : Nat.card H = Nat.card K) : H = K := by
  classical
  have key : ∀ L : Subgroup G, ∀ a : G, a ∈ L ↔ a ^ Nat.card L = 1 := by
    intro L
    have hd : 0 < Nat.card L := Nat.card_pos
    have hfin : (Finset.univ.filter (fun a : G => a ∈ L)) =
        Finset.univ.filter (fun a : G => a ^ Nat.card L = 1) := by
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        rw [Finset.mem_filter] at ha ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 : ((⟨a, ha.2⟩ : L) ^ Nat.card L : L) = 1 := pow_card_eq_one'
        have h2 := congrArg (fun x : L => (x : G)) h1
        simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
      · calc (Finset.univ.filter (fun a : G => a ^ Nat.card L = 1)).card
            ≤ Nat.card L := IsCyclic.card_pow_eq_one_le hd
          _ = (Finset.univ.filter (fun a : G => a ∈ L)).card := by
            rw [Nat.card_eq_fintype_card]
            exact Fintype.card_subtype _
    intro a
    have := congrArg (a ∈ ·) hfin
    simpa using this
  ext a
  rw [key H, key K, h]

theorem cyclic_of_perfect_is_leinster (G : Type*) [Group G] [Fintype G]
    [IsCyclic G] (h_perfect : Nat.Perfect (Fintype.card G)) :
    IsLeinster G := by
  classical
  unfold IsLeinster
  have hn : 0 < Fintype.card G := Fintype.card_pos
  rw [← (Nat.perfect_iff_sum_divisors_eq_two_mul hn).1 h_perfect]
  refine Finset.sum_bij (fun H _ => Nat.card H.1) ?_ ?_ ?_ ?_
  · intro H _
    rw [Nat.mem_divisors]
    refine ⟨?_, hn.ne'⟩
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H.1
  · intro H _ K _ hHK
    exact Subtype.ext (cyclicLeinster_subgroup_eq_of_card_eq H.1 K.1 hHK)
  · intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hog : orderOf g = Fintype.card G := by
      rw [← Nat.card_eq_fintype_card]; exact orderOf_eq_card_of_forall_mem_zpowers hg
    refine ⟨⟨Subgroup.zpowers (g ^ (orderOf g / d)), Subgroup.normal_of_isMulCommutative _⟩,
      Finset.mem_univ _, ?_⟩
    simp only
    rw [Nat.card_zpowers, orderOf_pow_orderOf_div (by omega) (hog ▸ hd.1)]
  · intro H _
    rfl

end OpenProofs.LeinsterGroup
