import FormalConjectures.Wikipedia.Kaplansky

/-!
# `Kaplansky.promislow_group_is_torsionfree`

Upstream: `Kaplansky.promislow_group_is_torsionfree` (category API), `FormalConjectures/Wikipedia/Kaplansky.lean` line 100.
Proof idea: with `x = a²`, `y = b²`, `z = (ab)²`, the relations show that `x, y, z` commute and
that every element of the Promislow group is `x^i y^j z^k t` with `t ∈ {1, a, b, ab}` (closure
of these normal forms under right multiplication by `a^{±1}`, `b^{±1}`). The group acts on `ℤ³`
by `a(u,v,w) = (u+1, 1-v, -w)`, `b(u,v,w) = (-u, v+1, 1-w)`. For each normal form some
coordinate is moved by a constant translation: `2i+1` (first coordinate) if `t = a`, `2j+1`
(second) if `t = b`, `-2k-1` (third) if `t = ab`, and `(2i, 2j, -2k)` if `t = 1`. If `g^n = 1`
with `n > 0`, these translations times `n` vanish, which forces `t = 1` and `i = j = k = 0`.
-/

open Kaplansky

namespace OpenProofs.Kaplansky

section PromislowAux

variable {M : Type*} [Group M]

theorem promislow_combine {x y z : M} (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) (i j k p q r : ℤ) (t : M) :
    x ^ i * y ^ j * z ^ k * (x ^ p * y ^ q * z ^ r * t) =
      x ^ (i + p) * y ^ (j + q) * z ^ (k + r) * t := by
  have e1 : y ^ j * z ^ k * x ^ p = x ^ p * (y ^ j * z ^ k) :=
    (((hxy.zpow_zpow p j).mul_right (hxz.zpow_zpow p k)).eq).symm
  have e2 : z ^ k * y ^ q = y ^ q * z ^ k := ((hyz.zpow_zpow q k).eq).symm
  rw [zpow_add, zpow_add, zpow_add]
  calc x ^ i * y ^ j * z ^ k * (x ^ p * y ^ q * z ^ r * t)
      = x ^ i * (y ^ j * z ^ k * x ^ p) * y ^ q * z ^ r * t := by simp only [mul_assoc]
    _ = x ^ i * (x ^ p * (y ^ j * z ^ k)) * y ^ q * z ^ r * t := by rw [e1]
    _ = x ^ i * x ^ p * y ^ j * (z ^ k * y ^ q) * z ^ r * t := by simp only [mul_assoc]
    _ = x ^ i * x ^ p * y ^ j * (y ^ q * z ^ k) * z ^ r * t := by rw [e2]
    _ = x ^ i * x ^ p * (y ^ j * y ^ q) * (z ^ k * z ^ r) * t := by simp only [mul_assoc]

theorem promislow_step {x y z s : M} {T : M → Prop} (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z)
    (H : ∀ t, T t → ∃ (p q r : ℤ) (t' : M), T t' ∧ t * s = x ^ p * y ^ q * z ^ r * t')
    {g : M} (hg : ∃ (i j k : ℤ) (t : M), T t ∧ g = x ^ i * y ^ j * z ^ k * t) :
    ∃ (i j k : ℤ) (t : M), T t ∧ g * s = x ^ i * y ^ j * z ^ k * t := by
  obtain ⟨i, j, k, t, ht, rfl⟩ := hg
  obtain ⟨p, q, r, t', ht', e⟩ := H t ht
  refine ⟨i + p, j + q, k + r, t', ht', ?_⟩
  rw [show x ^ i * y ^ j * z ^ k * t * s = x ^ i * y ^ j * z ^ k * (t * s) from mul_assoc _ _ _,
    e, promislow_combine hxy hxz hyz]

variable {a b : M}

theorem promislow_M1 (h1 : b⁻¹ * a * a * b * a * a = 1) : a * a * b = b * (a * a)⁻¹ := by
  calc a * a * b = b * (a * a)⁻¹ * (a * a * (b⁻¹ * a * a * b * a * a) * (a * a)⁻¹) := by group
    _ = b * (a * a)⁻¹ := by rw [h1]; group

theorem promislow_M1' (h1 : b⁻¹ * a * a * b * a * a = 1) : b * (a * a) = (a * a)⁻¹ * b := by
  calc b * (a * a) = (a * a)⁻¹ * b * (b⁻¹ * a * a * b * a * a) := by group
    _ = (a * a)⁻¹ * b := by rw [h1, mul_one]

theorem promislow_M2 (h2 : a⁻¹ * b * b * a * b * b = 1) : b * b * a = a * (b * b)⁻¹ := by
  calc b * b * a = a * (b * b)⁻¹ * (b * b * (a⁻¹ * b * b * a * b * b) * (b * b)⁻¹) := by group
    _ = a * (b * b)⁻¹ := by rw [h2]; group

theorem promislow_M2' (h2 : a⁻¹ * b * b * a * b * b = 1) : a * (b * b) = (b * b)⁻¹ * a := by
  calc a * (b * b) = (b * b)⁻¹ * a * (a⁻¹ * b * b * a * b * b) := by group
    _ = (b * b)⁻¹ * a := by rw [h2, mul_one]

theorem promislow_comm_xy (h1 : b⁻¹ * a * a * b * a * a = 1) : Commute (a * a) (b * b) := by
  show a * a * (b * b) = b * b * (a * a)
  calc a * a * (b * b) = a * a * b * b := by group
    _ = b * (a * a)⁻¹ * b := by rw [promislow_M1 h1]
    _ = b * ((a * a)⁻¹ * b) := by group
    _ = b * (b * (a * a)) := by rw [promislow_M1' h1]
    _ = b * b * (a * a) := by group

theorem promislow_comm_xz (h1 : b⁻¹ * a * a * b * a * a = 1) :
    Commute (a * a) (a * b * a * b) := by
  show a * a * (a * b * a * b) = a * b * a * b * (a * a)
  calc a * a * (a * b * a * b) = a * (a * a * b) * a * b := by group
    _ = a * (b * (a * a)⁻¹) * a * b := by rw [promislow_M1 h1]
    _ = a * b * a * ((a * a)⁻¹ * b) := by group
    _ = a * b * a * (b * (a * a)) := by rw [promislow_M1' h1]
    _ = a * b * a * b * (a * a) := by group

theorem promislow_comm_yz (h2 : a⁻¹ * b * b * a * b * b = 1) :
    Commute (b * b) (a * b * a * b) := by
  show b * b * (a * b * a * b) = a * b * a * b * (b * b)
  calc b * b * (a * b * a * b) = b * b * a * b * a * b := by group
    _ = a * (b * b)⁻¹ * b * a * b := by rw [promislow_M2 h2]
    _ = a * b * ((b * b)⁻¹ * a) * b := by group
    _ = a * b * (a * (b * b)) * b := by rw [promislow_M2' h2]
    _ = a * b * a * b * (b * b) := by group

theorem promislow_N6 (h2 : a⁻¹ * b * b * a * b * b = 1) :
    a * b * a = (b * b)⁻¹ * (a * b * a * b) * b := by
  calc a * b * a = a * b * (a * (b * b)⁻¹) * (b * b) := by group
    _ = a * b * (b * b * a) * (b * b) := by rw [promislow_M2 h2]
    _ = a * (b * b) * b * a * (b * b) := by group
    _ = (b * b)⁻¹ * a * b * a * (b * b) := by rw [promislow_M2' h2]
    _ = (b * b)⁻¹ * (a * b * a * b) * b := by group

/-- The normal-form tails. -/
def PromislowTail (a b t : M) : Prop := t = 1 ∨ t = a ∨ t = b ∨ t = a * b

theorem promislow_H_a (h1 : b⁻¹ * a * a * b * a * a = 1) (h2 : a⁻¹ * b * b * a * b * b = 1) :
    ∀ t, PromislowTail a b t → ∃ (p q r : ℤ) (t' : M), PromislowTail a b t' ∧
      t * a = (a * a) ^ p * (b * b) ^ q * (a * b * a * b) ^ r * t' := by
  rintro t (h | h | h | h) <;> subst t
  · exact ⟨0, 0, 0, a, by simp [PromislowTail], by group⟩
  · exact ⟨1, 0, 0, 1, by simp [PromislowTail], by group⟩
  · refine ⟨-1, 1, -1, a * b, by simp [PromislowTail], ?_⟩
    calc b * a = (a * a)⁻¹ * (a * a * b) * a := by group
      _ = (a * a)⁻¹ * (b * (a * a)⁻¹) * a := by rw [promislow_M1 h1]
      _ = _ := by group
  · refine ⟨0, -1, 1, b, by simp [PromislowTail], ?_⟩
    exact (promislow_N6 h2).trans (by group)

theorem promislow_H_b (h2 : a⁻¹ * b * b * a * b * b = 1) :
    ∀ t, PromislowTail a b t → ∃ (p q r : ℤ) (t' : M), PromislowTail a b t' ∧
      t * b = (a * a) ^ p * (b * b) ^ q * (a * b * a * b) ^ r * t' := by
  rintro t (h | h | h | h) <;> subst t
  · exact ⟨0, 0, 0, b, by simp [PromislowTail], by group⟩
  · exact ⟨0, 0, 0, a * b, by simp [PromislowTail], by group⟩
  · exact ⟨0, 1, 0, 1, by simp [PromislowTail], by group⟩
  · refine ⟨0, -1, 0, a, by simp [PromislowTail], ?_⟩
    calc a * b * b = a * (b * b) := by group
      _ = (b * b)⁻¹ * a := by rw [promislow_M2' h2]
      _ = _ := by group

theorem promislow_H_ainv (h1 : b⁻¹ * a * a * b * a * a = 1) (h2 : a⁻¹ * b * b * a * b * b = 1) :
    ∀ t, PromislowTail a b t → ∃ (p q r : ℤ) (t' : M), PromislowTail a b t' ∧
      t * a⁻¹ = (a * a) ^ p * (b * b) ^ q * (a * b * a * b) ^ r * t' := by
  rintro t (h | h | h | h) <;> subst t
  · exact ⟨-1, 0, 0, a, by simp [PromislowTail], by group⟩
  · exact ⟨0, 0, 0, 1, by simp [PromislowTail], by group⟩
  · exact ⟨0, 1, -1, a * b, by simp [PromislowTail], by group⟩
  · refine ⟨1, -1, 1, b, by simp [PromislowTail], ?_⟩
    calc a * b * a⁻¹ = a * (b * (a * a)⁻¹) * a := by group
      _ = a * (a * a * b) * a := by rw [← promislow_M1 h1]
      _ = (a * a) * (a * b * a) := by group
      _ = (a * a) * ((b * b)⁻¹ * (a * b * a * b) * b) := by rw [← promislow_N6 h2]
      _ = _ := by group

theorem promislow_H_binv (h2 : a⁻¹ * b * b * a * b * b = 1) :
    ∀ t, PromislowTail a b t → ∃ (p q r : ℤ) (t' : M), PromislowTail a b t' ∧
      t * b⁻¹ = (a * a) ^ p * (b * b) ^ q * (a * b * a * b) ^ r * t' := by
  rintro t (h | h | h | h) <;> subst t
  · exact ⟨0, -1, 0, b, by simp [PromislowTail], by group⟩
  · refine ⟨0, 1, 0, a * b, by simp [PromislowTail], ?_⟩
    calc a * b⁻¹ = a * (b * b)⁻¹ * b := by group
      _ = b * b * a * b := by rw [← promislow_M2 h2]
      _ = _ := by group
  · exact ⟨0, 0, 0, 1, by simp [PromislowTail], by group⟩
  · exact ⟨0, 0, 0, a, by simp [PromislowTail], by group⟩

theorem promislow_nf_of_mem_closure (h1 : b⁻¹ * a * a * b * a * a = 1)
    (h2 : a⁻¹ * b * b * a * b * b = 1) {g : M} (hg : g ∈ Subgroup.closure ({a, b} : Set M)) :
    ∃ (i j k : ℤ) (t : M), PromislowTail a b t ∧
      g = (a * a) ^ i * (b * b) ^ j * (a * b * a * b) ^ k * t := by
  have hxy := promislow_comm_xy h1
  have hxz := promislow_comm_xz h1
  have hyz := promislow_comm_yz h2
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, 0, 0, 1, Or.inl rfl, by group⟩
  | mul_right x _ y hy ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact promislow_step hxy hxz hyz (promislow_H_a h1 h2) ih
    · exact promislow_step hxy hxz hyz (promislow_H_b h2) ih
  | mul_inv_cancel x _ y hy ih =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact promislow_step hxy hxz hyz (promislow_H_ainv h1 h2) ih
    · exact promislow_step hxy hxz hyz (promislow_H_binv h2) ih

end PromislowAux

section PromislowAction

/-- The action of `a` on `ℤ³`. -/
def promislowActA : Equiv.Perm (ℤ × ℤ × ℤ) where
  toFun p := (p.1 + 1, 1 - p.2.1, -p.2.2)
  invFun p := (p.1 - 1, 1 - p.2.1, -p.2.2)
  left_inv p := by obtain ⟨u, v, w⟩ := p; simp only [Prod.mk.injEq]; omega
  right_inv p := by obtain ⟨u, v, w⟩ := p; simp only [Prod.mk.injEq]; omega

/-- The action of `b` on `ℤ³`. -/
def promislowActB : Equiv.Perm (ℤ × ℤ × ℤ) where
  toFun p := (-p.1, p.2.1 + 1, 1 - p.2.2)
  invFun p := (-p.1, p.2.1 - 1, 1 - p.2.2)
  left_inv p := by obtain ⟨u, v, w⟩ := p; simp only [Prod.mk.injEq]; omega
  right_inv p := by obtain ⟨u, v, w⟩ := p; simp only [Prod.mk.injEq]; omega

theorem promislowActA_apply (p : ℤ × ℤ × ℤ) :
    promislowActA p = (p.1 + 1, 1 - p.2.1, -p.2.2) := rfl

theorem promislowActA_symm_apply (p : ℤ × ℤ × ℤ) :
    promislowActA.symm p = (p.1 - 1, 1 - p.2.1, -p.2.2) := rfl

theorem promislowActB_symm_apply (p : ℤ × ℤ × ℤ) :
    promislowActB.symm p = (-p.1, p.2.1 - 1, 1 - p.2.2) := rfl

theorem promislowActB_apply (p : ℤ × ℤ × ℤ) :
    promislowActB p = (-p.1, p.2.1 + 1, 1 - p.2.2) := rfl

theorem promislow_rels :
    ∀ r ∈ ({(FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 1 *
        FreeGroup.of 0 * FreeGroup.of 0,
      (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 * FreeGroup.of 0 *
        FreeGroup.of 1 * FreeGroup.of 1} : Set (FreeGroup (Fin 2))),
      FreeGroup.lift ![promislowActA, promislowActB] r = 1 := by
  intro r hr
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl <;>
  · ext ⟨u, v, w⟩ <;>
      simp [promislowActA_apply, promislowActB_apply, promislowActA_symm_apply,
        promislowActB_symm_apply]

/-- The affine action of the Promislow group on `ℤ³`. -/
def promislowRep : PromislowGroup →* Equiv.Perm (ℤ × ℤ × ℤ) :=
  PresentedGroup.toGroup promislow_rels

theorem promislowRep_a : promislowRep (PresentedGroup.of 0) = promislowActA :=
  PresentedGroup.toGroup.of promislow_rels

theorem promislowRep_b : promislowRep (PresentedGroup.of 1) = promislowActB :=
  PresentedGroup.toGroup.of promislow_rels

theorem promislow_transBy_zpow {π : ℤ × ℤ × ℤ → ℤ} {h : Equiv.Perm (ℤ × ℤ × ℤ)} {c : ℤ}
    (hc : ∀ p, π (h p) = π p + c) (n : ℤ) : ∀ p, π ((h ^ n) p) = π p + n * c := by
  induction n using Int.induction_on with
  | zero => intro p; simp
  | succ n ih =>
    intro p
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hc]
    ring
  | pred n ih =>
    intro p
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    have := hc (h⁻¹ p)
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
    linarith

theorem promislow_transBy_nf {π : ℤ × ℤ × ℤ → ℤ} {X Y Z T : Equiv.Perm (ℤ × ℤ × ℤ)}
    {cx cy cz ct : ℤ} (hX : ∀ p, π (X p) = π p + cx) (hY : ∀ p, π (Y p) = π p + cy)
    (hZ : ∀ p, π (Z p) = π p + cz) (hT : ∀ p, π (T p) = π p + ct) (i j k : ℤ) :
    ∀ p, π ((X ^ i * Y ^ j * Z ^ k * T) p) = π p + (i * cx + j * cy + k * cz + ct) := by
  intro p
  simp only [Equiv.Perm.mul_apply]
  rw [promislow_transBy_zpow hX, promislow_transBy_zpow hY, promislow_transBy_zpow hZ, hT]
  ring

end PromislowAction

variable (K : Type*) [Field K]
variable (G : Type*) [Group G] (hG : Monoid.IsTorsionFree G)

theorem promislow_group_is_torsionfree :
    Monoid.IsTorsionFree PromislowGroup := by
  have h1 : (PresentedGroup.of 1 : PromislowGroup)⁻¹ * PresentedGroup.of 0 *
      PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 * PresentedGroup.of 0 = 1 := by
    have := PresentedGroup.one_of_mem (rels := ({(FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of 0 *
        FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 0,
      (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 * FreeGroup.of 0 *
        FreeGroup.of 1 * FreeGroup.of 1} : Set (FreeGroup (Fin 2)))) (Set.mem_insert _ _)
    simp only [map_mul, map_inv] at this
    exact this
  have h2 : (PresentedGroup.of 0 : PromislowGroup)⁻¹ * PresentedGroup.of 1 *
      PresentedGroup.of 1 * PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 1 = 1 := by
    have := PresentedGroup.one_of_mem (rels := ({(FreeGroup.of (1 : Fin 2))⁻¹ * FreeGroup.of 0 *
        FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 0,
      (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 * FreeGroup.of 0 *
        FreeGroup.of 1 * FreeGroup.of 1} : Set (FreeGroup (Fin 2))))
      (Set.mem_insert_of_mem _ rfl)
    simp only [map_mul, map_inv] at this
    exact this
  intro g hg hfin
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have hcl : g ∈ Subgroup.closure ({PresentedGroup.of 0, PresentedGroup.of 1} :
      Set PromislowGroup) :=
    PresentedGroup.generated_by _ _
      (fun j => by fin_cases j <;> exact Subgroup.subset_closure (by simp)) g
  obtain ⟨i, j, k, t, ht, rfl⟩ := promislow_nf_of_mem_closure h1 h2 hcl
  have key : ∀ (π : ℤ × ℤ × ℤ → ℤ) (c : ℤ),
      (∀ p, π (promislowRep ((PresentedGroup.of 0 * PresentedGroup.of 0) ^ i *
        (PresentedGroup.of 1 * PresentedGroup.of 1) ^ j *
        (PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 *
          PresentedGroup.of 1) ^ k * t) p) = π p + c) → c = 0 := by
    intro π c hc
    have := promislow_transBy_zpow hc n (0, 0, 0)
    rw [zpow_natCast, ← map_pow, hgn, map_one, Equiv.Perm.one_apply] at this
    have hnc : (n : ℤ) * c = 0 := by linarith
    rcases mul_eq_zero.1 hnc with h | h
    · omega
    · exact h
  have hrep : ∀ s : PromislowGroup, promislowRep ((PresentedGroup.of 0 * PresentedGroup.of 0) ^ i *
        (PresentedGroup.of 1 * PresentedGroup.of 1) ^ j *
        (PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 *
          PresentedGroup.of 1) ^ k * s) =
      (promislowActA * promislowActA) ^ i * (promislowActB * promislowActB) ^ j *
        (promislowActA * promislowActB * promislowActA * promislowActB) ^ k * promislowRep s := by
    intro s
    simp only [map_mul, map_zpow, promislowRep_a, promislowRep_b]
  simp only [hrep] at key
  have x1 : ∀ p, ((promislowActA * promislowActA) p).1 = p.1 + 2 := by
    intro p; simp [promislowActA_apply]; ring
  have x2 : ∀ p, ((promislowActA * promislowActA) p).2.1 = p.2.1 + 0 := by
    intro p; simp [promislowActA_apply]
  have x3 : ∀ p, ((promislowActA * promislowActA) p).2.2 = p.2.2 + 0 := by
    intro p; simp [promislowActA_apply]
  have y1 : ∀ p, ((promislowActB * promislowActB) p).1 = p.1 + 0 := by
    intro p; simp [promislowActB_apply]
  have y2 : ∀ p, ((promislowActB * promislowActB) p).2.1 = p.2.1 + 2 := by
    intro p; simp [promislowActB_apply]; ring
  have y3 : ∀ p, ((promislowActB * promislowActB) p).2.2 = p.2.2 + 0 := by
    intro p; simp [promislowActB_apply]
  have z1 : ∀ p, ((promislowActA * promislowActB * promislowActA * promislowActB) p).1 =
      p.1 + 0 := by
    intro p; simp [promislowActA_apply, promislowActB_apply]
  have z2 : ∀ p, ((promislowActA * promislowActB * promislowActA * promislowActB) p).2.1 =
      p.2.1 + 0 := by
    intro p; simp [promislowActA_apply, promislowActB_apply]
  have z3 : ∀ p, ((promislowActA * promislowActB * promislowActA * promislowActB) p).2.2 =
      p.2.2 + -2 := by
    intro p; simp [promislowActA_apply, promislowActB_apply]; ring
  have t1 : ∀ (π : ℤ × ℤ × ℤ → ℤ) p, π (promislowRep 1 p) = π p + 0 := by simp
  have ta : ∀ p, (promislowRep (PresentedGroup.of 0) p).1 = p.1 + 1 := by
    intro p; rw [promislowRep_a, promislowActA_apply]
  have tb : ∀ p, (promislowRep (PresentedGroup.of 1) p).2.1 = p.2.1 + 1 := by
    intro p; rw [promislowRep_b, promislowActB_apply]
  have tab : ∀ p, (promislowRep (PresentedGroup.of 0 * PresentedGroup.of 1) p).2.2 =
      p.2.2 + -1 := by
    intro p
    rw [map_mul, promislowRep_a, promislowRep_b, Equiv.Perm.mul_apply, promislowActA_apply,
      promislowActB_apply]
    ring
  rcases ht with rfl | rfl | rfl | rfl
  · have e1 := key Prod.fst _
      (promislow_transBy_nf (π := Prod.fst) x1 y1 z1 (t1 Prod.fst) i j k)
    have e2 := key (fun p => p.2.1) _
      (promislow_transBy_nf (π := fun p => p.2.1) x2 y2 z2 (t1 (fun p => p.2.1)) i j k)
    have e3 := key (fun p => p.2.2) _
      (promislow_transBy_nf (π := fun p => p.2.2) x3 y3 z3 (t1 (fun p => p.2.2)) i j k)
    apply hg
    obtain rfl : i = 0 := by linarith
    obtain rfl : j = 0 := by linarith
    obtain rfl : k = 0 := by linarith
    simp
  · have e := key Prod.fst _ (promislow_transBy_nf (π := Prod.fst) x1 y1 z1 ta i j k)
    omega
  · have e := key (fun p => p.2.1) _
      (promislow_transBy_nf (π := fun p => p.2.1) x2 y2 z2 tb i j k)
    omega
  · have e := key (fun p => p.2.2) _
      (promislow_transBy_nf (π := fun p => p.2.2) x3 y3 z3 tab i j k)
    omega

end OpenProofs.Kaplansky
