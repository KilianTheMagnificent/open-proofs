import FormalConjectures.ErdosProblems.«1171»

/-!
# `Erdos1171.erdos_1171.variants.mono_k`

Upstream: `Erdos1171.erdos_1171.variants.mono_k` (category API), `FormalConjectures/ErdosProblems/1171.lean` line 62.
Proof idea: the hypothesis and the conclusion live in independent universes, so we prove a
transfer lemma. If `lift α = lift α'`, `lift β = lift β'`, `lift γ = lift γ'`, `1 < γ` and
`j ≤ k`, then the `k`-color relation for `(α, β, γ)` gives the `j`-color relation for
`(α', β', γ')`. An order isomorphism `e : α.ToType ≃o α'.ToType` comes from
`Ordinal.lift_type_eq`. A `(j+1)`-coloring `col` of pairs of `α'` pulls back along `Sym2.map e`
and is cast into `Fin (k+1)` with `Fin.castLE`. A color-0 set `A` maps to `e '' A`, which has the
same order type up to lifting. A set `A` with `#A = γ > 1` monochromatic in color `i.succ`
contains two distinct points, so `i.succ` is a cast value of `col` and `i < j`; its image is
monochromatic in color `(⟨i, _⟩ : Fin j).succ` and has cardinality `γ'`. For the target,
`ω_ 1 ^ 2`, `ω_ 1 * ω` and `3` lift to the same values in every universe.
-/

open Cardinal Ordinal SimpleGraph
open Erdos1171.erdos_1171.variants

namespace OpenProofs.Erdos1171.erdos_1171.variants

universe u v

theorem omcr_transfer_mono_k_p1171 {α β : Ordinal.{u}} {α' β' : Ordinal.{v}}
    {γ : Cardinal.{u}} {γ' : Cardinal.{v}} {j k : ℕ} (hjk : j ≤ k)
    (hα : Ordinal.lift.{v} α = Ordinal.lift.{u} α')
    (hβ : Ordinal.lift.{v} β = Ordinal.lift.{u} β')
    (hγ : Cardinal.lift.{v} γ = Cardinal.lift.{u} γ') (hγ1 : 1 < γ)
    (h : OrdinalMultiColorRamsey α β γ k) : OrdinalMultiColorRamsey α' β' γ' j := by
  have hiso : Nonempty (((· < ·) : α.ToType → α.ToType → Prop) ≃r
      ((· < ·) : α'.ToType → α'.ToType → Prop)) := by
    rw [← Ordinal.lift_type_eq.{u, v, 0}]
    simpa only [Ordinal.type_toType] using hα
  obtain ⟨f⟩ := hiso
  let e : α.ToType ≃o α'.ToType := OrderIso.ofRelIsoLT f
  intro col
  have hle : j + 1 ≤ k + 1 := by omega
  rcases h (fun p => Fin.castLE hle (col (Sym2.map e p))) with ⟨A, hA, hAt⟩ | ⟨i, A, hA, hAc⟩
  · left
    refine ⟨e '' A, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      have hne : x ≠ y := fun h => hxy (congrArg e h)
      have h := congrArg Fin.val (hA x hx y hy hne)
      simp only [Sym2.map_mk, Fin.val_castLE] at h
      exact Fin.ext (by simpa using h)
    · have hA' : Nonempty (((· < ·) : A → A → Prop) ≃r
          ((· < ·) : (e '' A) → (e '' A) → Prop)) :=
        ⟨⟨e.toEquiv.image A, by
          intro a b
          change e a.1 < e b.1 ↔ a < b
          rw [e.lt_iff_lt]
          rfl⟩⟩
      have hl := Ordinal.lift_type_eq.{u, v, 0}.2 hA'
      rw [← Ordinal.lift_inj.{u, v}, ← hβ, ← hAt]
      exact hl.symm
  · right
    have h1 : 1 < #A := hAc ▸ hγ1
    obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ A, ∃ y ∈ A, x ≠ y := by
      rw [Cardinal.one_lt_iff_nontrivial] at h1
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne⟩ := h1
      exact ⟨x, hx, y, hy, fun h => hne (Subtype.ext h)⟩
    have hv := congrArg Fin.val (hA x hx y hy hxy)
    simp only [Fin.val_castLE, Fin.val_succ] at hv
    have hij : (i : ℕ) < j := by
      have := (col (Sym2.map e s(x, y))).isLt
      omega
    refine ⟨⟨i, hij⟩, e '' A, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      have hne : a ≠ b := fun h => hab (congrArg e h)
      have h := congrArg Fin.val (hA a ha b hb hne)
      simp only [Sym2.map_mk, Fin.val_castLE, Fin.val_succ] at h
      exact Fin.ext (by simpa using h)
    · rw [← Cardinal.lift_inj.{v, u}, Cardinal.mk_image_eq_lift _ _ e.injective, hAc, hγ]

theorem mono_k {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  refine omcr_transfer_mono_k_p1171 hjk ?_ ?_ ?_ (by norm_num) hk
  · simp [pow_two, Ordinal.lift_mul, Ordinal.lift_omega]
  · simp [Ordinal.lift_mul, Ordinal.lift_omega]
  · simp

end OpenProofs.Erdos1171.erdos_1171.variants
