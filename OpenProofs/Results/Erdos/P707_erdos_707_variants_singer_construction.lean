import FormalConjectures.ErdosProblems.«707»

/-!
# `Erdos707.erdos_707.variants.singer_construction`

Upstream: `Erdos707.erdos_707.variants.singer_construction` (category textbook), `FormalConjectures/ErdosProblems/707.lean` line 163.
Proof idea: Singer's construction. Write `p = r ^ k`, `q = p`, `n = q² + q + 1`, and let
`K = GaloisField r (3k)` (so `|K| = q³`) with a generator `g` of `Kˣ` (a primitive
`(q³ - 1)`-th root of unity). `F = {x | x ^ q = x}` has `q` elements (`0` and the `g ^ (n t)`),
and `L = F + F·g` has `q²`. Take `B = {i < n | g ^ i ∈ L}`. Splitting `L \ {0}` by exponents
modulo `n` gives `|B| (q - 1) = q² - 1`, so `|B| = q + 1`. Differences are injective: if
`a - b ≡ a' - b'` (mod `n`) with `a ≠ b`, then `c = g ^ (a' - a)` maps `g ^ a, g ^ b` into `L`,
and `g ^ a, g ^ b` span `L` over `F` (counting), so `c` preserves `L` and satisfies a monic
quadratic over `F`; then `c, c ^ q, c ^ q²` are roots of it, and since `c ^ q³ = c` this forces
`c ^ q = c`, i.e. `n ∣ a' - a`, so `a = a'`, `b = b'`. Counting (`(q + 1) q = n - 1`) turns
injectivity into a bijection onto the nonzero residues.
-/

open Function Set
open Erdos707

namespace OpenProofs.Erdos707

namespace SingerAux

open Finset

variable {K : Type*} [Field K]

/-- The fixed points of `x ↦ x ^ q`. -/
def fixs (K : Type*) [Field K] [Fintype K] [DecidableEq K] (q : ℕ) : Finset K :=
  univ.filter (fun x => x ^ q = x)

/-- The span of `u, v` over the fixed points of `x ↦ x ^ q`. -/
def pspan [Fintype K] [DecidableEq K] (q : ℕ) (u v : K) : Finset K :=
  (fixs K q ×ˢ fixs K q).image (fun p => p.1 * u + p.2 * v)

lemma mem_fixs [Fintype K] [DecidableEq K] {q : ℕ} {x : K} : x ∈ fixs K q ↔ x ^ q = x := by
  simp [fixs]

lemma mem_pspan [Fintype K] [DecidableEq K] {q : ℕ} {u v x : K} :
    x ∈ pspan q u v ↔ ∃ α β : K, α ^ q = α ∧ β ^ q = β ∧ α * u + β * v = x := by
  simp only [pspan, Finset.mem_image, Finset.mem_product, mem_fixs, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h⟩; exact ⟨a, b, ha, hb, h⟩
  · rintro ⟨a, b, ha, hb, h⟩; exact ⟨a, b, ⟨ha, hb⟩, h⟩

lemma frob_sub {q : ℕ} (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) (x y : K) :
    (x - y) ^ q = x ^ q - y ^ q := by
  have h := hadd (x - y) y
  rw [sub_add_cancel] at h
  rw [h]; ring

lemma fix_sub {q : ℕ} (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) {x y : K}
    (hx : x ^ q = x) (hy : y ^ q = y) : (x - y) ^ q = x - y := by
  rw [frob_sub hadd, hx, hy]

lemma fix_add {q : ℕ} (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) {x y : K}
    (hx : x ^ q = x) (hy : y ^ q = y) : (x + y) ^ q = x + y := by
  rw [hadd, hx, hy]

lemma fix_mul {q : ℕ} {x y : K} (hx : x ^ q = x) (hy : y ^ q = y) : (x * y) ^ q = x * y := by
  rw [mul_pow, hx, hy]

lemma fix_div {q : ℕ} {x y : K} (hx : x ^ q = x) (hy : y ^ q = y) : (x / y) ^ q = x / y := by
  rw [div_pow, hx, hy]

lemma fix_zero {q : ℕ} (hq : q ≠ 0) : (0 : K) ^ q = 0 := zero_pow hq

lemma fix_neg {q : ℕ} (hq : q ≠ 0) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) {x : K}
    (hx : x ^ q = x) : (-x) ^ q = -x := by
  have := fix_sub hadd (fix_zero hq) hx
  simpa using this

/-- The algebraic heart: if multiplication by `c` preserves a two-dimensional space over the
fixed field, then `c` is in the fixed field (because `K` has degree three). -/
lemma core_fix [Fintype K] {q : ℕ} (hq : q ≠ 0) (hK : Fintype.card K = q ^ 3)
    (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    {c α β γ δ u v : K} (hα : α ^ q = α) (hβ : β ^ q = β) (hγ : γ ^ q = γ) (hδ : δ ^ q = δ)
    (hu : u ≠ 0) (h1 : c * u = α * u + β * v) (h2 : c * v = γ * u + δ * v) : c ^ q = c := by
  have hP : ∀ x : K, (x - α) * (x - δ) - β * γ = 0 →
      (x ^ q - α) * (x ^ q - δ) - β * γ = 0 := by
    intro x hx
    have e : ((x - α) * (x - δ) - β * γ) ^ q = (x ^ q - α) * (x ^ q - δ) - β * γ := by
      rw [frob_sub hadd, mul_pow, mul_pow, frob_sub hadd, frob_sub hadd, hα, hδ, hβ, hγ]
    rw [← e, hx, zero_pow hq]
  have hroot : ∀ r s : K, (r - α) * (r - δ) - β * γ = 0 → (s - α) * (s - δ) - β * γ = 0 →
      r = s ∨ r + s = α + δ := by
    intro r s hr hs
    have : (r - s) * (r + s - α - δ) = 0 := by linear_combination hr - hs
    rcases mul_eq_zero.mp this with h | h
    · left; exact sub_eq_zero.mp h
    · right; linear_combination h
  have hc : (c - α) * (c - δ) - β * γ = 0 := by
    have : ((c - α) * (c - δ) - β * γ) * u = 0 := by
      linear_combination (c - δ) * h1 + β * h2
    exact (mul_eq_zero.mp this).resolve_right hu
  have hb := hP c hc
  have hd := hP _ hb
  have h3 : ((c ^ q) ^ q) ^ q = c := by
    rw [← pow_mul, ← pow_mul, show q * (q * q) = Fintype.card K by rw [hK]; ring]
    exact FiniteField.pow_card c
  by_contra hne
  rcases hroot c (c ^ q) hc hb with h | h
  · exact hne h.symm
  rcases hroot c ((c ^ q) ^ q) hc hd with h' | h'
  · apply hne
    calc c ^ q = ((c ^ q) ^ q) ^ q := by rw [← h']
      _ = c := h3
  · have hbd : c ^ q = (c ^ q) ^ q := by linear_combination h - h'
    rw [← hbd, ← hbd] at h3
    exact hne h3

lemma cube_sub_one {q : ℕ} (hq : 1 ≤ q) : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add; ring

section Gen

variable {q : ℕ} {g : K}

lemma cube_ge (hq : 2 ≤ q) : 8 ≤ q ^ 3 := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3

lemma gen_ne_zero (hq : 2 ≤ q) (hg : IsPrimitiveRoot g (q ^ 3 - 1)) : g ≠ 0 :=
  hg.ne_zero (by have := cube_ge hq; omega)

lemma gpow_eq_iff (hq : 2 ≤ q) (hg : IsPrimitiveRoot g (q ^ 3 - 1)) {i j : ℕ} :
    g ^ i = g ^ j ↔ i ≡ j [MOD q ^ 3 - 1] := by
  have hfin : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨q ^ 3 - 1, by have := cube_ge hq; omega, hg.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hg.eq_orderOf]

lemma gpow_fix_iff (hq : 2 ≤ q) (hg : IsPrimitiveRoot g (q ^ 3 - 1)) (j : ℕ) :
    (g ^ j) ^ q = g ^ j ↔ q ^ 2 + q + 1 ∣ j := by
  have hN := cube_sub_one (q := q) (by omega)
  have hg0 := gen_ne_zero hq hg
  have e : (g ^ j) ^ q = g ^ j * g ^ (j * (q - 1)) := by
    rw [← pow_mul, ← pow_add]; congr 1
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  rw [e, mul_eq_left₀ (pow_ne_zero _ hg0), hg.pow_eq_one_iff_dvd, hN]
  exact Nat.mul_dvd_mul_iff_right (by omega)

lemma gpow_surj [Fintype K] (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 3) (hg : IsPrimitiveRoot g (q ^ 3 - 1))
    {x : K} (hx : x ≠ 0) : ∃ j < q ^ 3 - 1, g ^ j = x := by
  have : NeZero (q ^ 3 - 1) := ⟨by have := cube_ge hq; omega⟩
  apply hg.eq_pow_of_pow_eq_one
  rw [← hK]; exact FiniteField.pow_card_sub_one_eq_one x hx

lemma card_fixs [Fintype K] [DecidableEq K] (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 3) (hg : IsPrimitiveRoot g (q ^ 3 - 1)) :
    (fixs K q).card = q := by
  have hN := cube_sub_one (q := q) (by omega)
  have hg0 := gen_ne_zero hq hg
  have hn : 0 < q ^ 2 + q + 1 := by positivity
  have hset : fixs K q = insert 0 ((Finset.range (q - 1)).image (fun t => g ^ ((q ^ 2 + q + 1) * t))) := by
    ext x
    simp only [mem_fixs, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      by_cases h0 : x = 0
      · left; exact h0
      · right
        obtain ⟨j, hj, rfl⟩ := gpow_surj hq hK hg h0
        obtain ⟨t, rfl⟩ := (gpow_fix_iff hq hg j).mp hx
        refine ⟨t, ?_, rfl⟩
        rw [hN] at hj
        exact Nat.lt_of_mul_lt_mul_left hj
    · rintro (rfl | ⟨t, -, rfl⟩)
      · exact zero_pow (by omega)
      · exact (gpow_fix_iff hq hg _).mpr (dvd_mul_right _ _)
  rw [hset, Finset.card_insert_of_notMem, Finset.card_image_of_injOn]
  · simp; omega
  · intro t ht t' ht' h
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    have hlt : ∀ s, s < q - 1 → (q ^ 2 + q + 1) * s < q ^ 3 - 1 := by
      intro s hs; rw [hN]; exact Nat.mul_lt_mul_of_pos_left hs hn
    have := hg.pow_inj (hlt t ht) (hlt t' ht') h
    exact Nat.eq_of_mul_eq_mul_left hn this
  · simp only [Finset.mem_image, not_exists, not_and]
    intro t _ h
    exact pow_ne_zero _ hg0 h

end Gen

section Line

variable {q : ℕ} {g : K}

lemma smul_mem_pspan [Fintype K] [DecidableEq K] {u v x f : K} (hf : f ^ q = f)
    (hx : x ∈ pspan q u v) : f * x ∈ pspan q u v := by
  obtain ⟨α, β, hα, hβ, rfl⟩ := mem_pspan.mp hx
  exact mem_pspan.mpr ⟨f * α, f * β, fix_mul hf hα, fix_mul hf hβ, by ring⟩

lemma pspan_subset [Fintype K] [DecidableEq K] (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    {u v u' v' : K} (hu : u ∈ pspan q u' v') (hv : v ∈ pspan q u' v') :
    pspan q u v ⊆ pspan q u' v' := by
  intro x hx
  obtain ⟨α, β, hα, hβ, rfl⟩ := mem_pspan.mp hx
  obtain ⟨a1, b1, ha1, hb1, rfl⟩ := mem_pspan.mp hu
  obtain ⟨a2, b2, ha2, hb2, rfl⟩ := mem_pspan.mp hv
  exact mem_pspan.mpr ⟨α * a1 + β * a2, α * b1 + β * b2,
    fix_add hadd (fix_mul hα ha1) (fix_mul hβ ha2),
    fix_add hadd (fix_mul hα hb1) (fix_mul hβ hb2), by ring⟩

lemma card_pspan [Fintype K] [DecidableEq K] (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 3)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    {u v : K}
    (hind : ∀ α β : K, α ^ q = α → β ^ q = β → α * u + β * v = 0 → α = 0 ∧ β = 0) :
    (pspan q u v).card = q * q := by
  rw [pspan, Finset.card_image_of_injOn, Finset.card_product, card_fixs hq hK hg]
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_fixs] at hab hab'
  simp only at h
  obtain ⟨h1, h2⟩ := hind (a - a') (b - b') (fix_sub hadd hab.1 hab'.1)
    (fix_sub hadd hab.2 hab'.2) (by linear_combination h)
  exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)

lemma card_pspan_le [Fintype K] [DecidableEq K] (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 3)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) {u v : K} : (pspan q u v).card ≤ q * q := by
  calc (pspan q u v).card ≤ (fixs K q ×ˢ fixs K q).card := Finset.card_image_le
    _ = q * q := by rw [Finset.card_product, card_fixs hq hK hg]

lemma pspan_eq [Fintype K] [DecidableEq K] (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 3)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    {u v u' v' : K} (hu : u ∈ pspan q u' v') (hv : v ∈ pspan q u' v')
    (hind : ∀ α β : K, α ^ q = α → β ^ q = β → α * u + β * v = 0 → α = 0 ∧ β = 0) :
    pspan q u v = pspan q u' v' :=
  Finset.eq_of_subset_of_card_le (pspan_subset hadd hu hv)
    (by rw [card_pspan hq hK hg hadd hind]; exact card_pspan_le hq hK hg)

lemma indep_of (hq : q ≠ 0) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q) {u v : K}
    (hu : u ≠ 0) (h : ∀ f : K, f ^ q = f → v ≠ f * u) :
    ∀ α β : K, α ^ q = α → β ^ q = β → α * u + β * v = 0 → α = 0 ∧ β = 0 := by
  intro α β hα hβ e
  by_cases hβ0 : β = 0
  · subst hβ0
    simp only [zero_mul, add_zero] at e
    exact ⟨(mul_eq_zero.mp e).resolve_right hu, rfl⟩
  · exfalso
    apply h (-α / β) (fix_div (fix_neg hq hadd hα) hβ)
    field_simp
    linear_combination e

lemma indep_gpow [Fintype K] (hq : 2 ≤ q) (hK : Fintype.card K = q ^ 3)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) {a b : ℕ} (ha : a < q ^ 2 + q + 1)
    (hb : b < q ^ 2 + q + 1) (hab : a ≠ b) : ∀ f : K, f ^ q = f → g ^ a ≠ f * g ^ b := by
  intro f hf e
  have hg0 := gen_ne_zero hq hg
  have hf0 : f ≠ 0 := by
    rintro rfl; rw [zero_mul] at e; exact pow_ne_zero _ hg0 e
  obtain ⟨j, -, rfl⟩ := gpow_surj hq hK hg hf0
  obtain ⟨m, rfl⟩ := (gpow_fix_iff hq hg j).mp hf
  rw [← pow_add, gpow_eq_iff hq hg] at e
  have h2 : a ≡ (q ^ 2 + q + 1) * m + b [MOD q ^ 2 + q + 1] :=
    Nat.ModEq.of_dvd ⟨q - 1, cube_sub_one (by omega)⟩ e
  apply hab
  unfold Nat.ModEq at h2
  rwa [Nat.mul_add_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

lemma indep_one_gen (hq : 2 ≤ q) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) :
    ∀ α β : K, α ^ q = α → β ^ q = β → α * 1 + β * g = 0 → α = 0 ∧ β = 0 :=
  indep_of (by omega) hadd one_ne_zero (fun f hf e => by
    rw [mul_one] at e
    subst e
    have h1 := (gpow_fix_iff hq hg 1).mp (by rw [pow_one]; exact hf)
    have := Nat.le_of_dvd one_pos h1
    have : 0 < q ^ 2 := by positivity
    omega)

end Line

/-- The Singer set: exponents `i < q² + q + 1` with `g ^ i` on the line through `1` and `g`. -/
def singerD [Fintype K] [DecidableEq K] (q : ℕ) (g : K) : Finset ℕ :=
  (Finset.range (q ^ 2 + q + 1)).filter (fun i => g ^ i ∈ pspan q 1 g)

lemma mem_singerD [Fintype K] [DecidableEq K] {q : ℕ} {g : K} {i : ℕ} :
    i ∈ singerD q g ↔ i < q ^ 2 + q + 1 ∧ g ^ i ∈ pspan q 1 g := by
  simp [singerD]

lemma card_singerD [Fintype K] [DecidableEq K] {q : ℕ} {g : K} (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 3) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) : (singerD q g).card = q + 1 := by
  have hN : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := cube_sub_one (by omega)
  have hn : 0 < q ^ 2 + q + 1 := by positivity
  have hg0 := gen_ne_zero hq hg
  have hL0 : (0 : K) ∈ pspan q 1 g :=
    mem_pspan.mpr ⟨0, 0, fix_zero (by omega), fix_zero (by omega), by ring⟩
  have hLcard : (pspan q 1 g).card = q * q := card_pspan hq hK hg hadd (indep_one_gen hq hadd hg)
  have himg : (pspan q 1 g).erase 0 = (singerD q g ×ˢ Finset.range (q - 1)).image
      (fun p => g ^ (p.1 + (q ^ 2 + q + 1) * p.2)) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_product, Finset.mem_range,
      mem_singerD, Prod.exists]
    constructor
    · rintro ⟨hx0, hx⟩
      obtain ⟨j, hj, rfl⟩ := gpow_surj hq hK hg hx0
      have hjn : j / (q ^ 2 + q + 1) < q - 1 := by
        rw [Nat.div_lt_iff_lt_mul hn, mul_comm]; rw [hN] at hj; exact hj
      refine ⟨j % (q ^ 2 + q + 1), j / (q ^ 2 + q + 1), ⟨⟨Nat.mod_lt _ hn, ?_⟩, hjn⟩,
        by rw [Nat.mod_add_div]⟩
      have e : g ^ (j % (q ^ 2 + q + 1)) =
          g ^ ((q ^ 2 + q + 1) * (q - 1 - j / (q ^ 2 + q + 1))) * g ^ j := by
        have h1 : (q ^ 2 + q + 1) * (q - 1 - j / (q ^ 2 + q + 1)) + j =
            j % (q ^ 2 + q + 1) + (q ^ 3 - 1) := by
          rw [hN]
          have := Nat.mod_add_div j (q ^ 2 + q + 1)
          have h2 : (q ^ 2 + q + 1) * (q - 1 - j / (q ^ 2 + q + 1)) +
              (q ^ 2 + q + 1) * (j / (q ^ 2 + q + 1)) = (q ^ 2 + q + 1) * (q - 1) := by
            rw [← mul_add, Nat.sub_add_cancel hjn.le]
          omega
        rw [← pow_add, h1, pow_add, hg.pow_eq_one, mul_one]
      rw [e]
      exact smul_mem_pspan ((gpow_fix_iff hq hg _).mpr (dvd_mul_right _ _)) hx
    · rintro ⟨i, t, ⟨⟨_, hgi⟩, _⟩, rfl⟩
      refine ⟨pow_ne_zero _ hg0, ?_⟩
      rw [pow_add, mul_comm]
      exact smul_mem_pspan ((gpow_fix_iff hq hg _).mpr (dvd_mul_right _ _)) hgi
  have hinj : Set.InjOn (fun p : ℕ × ℕ => g ^ (p.1 + (q ^ 2 + q + 1) * p.2))
      ↑(singerD q g ×ˢ Finset.range (q - 1)) := by
    rintro ⟨i, t⟩ hit ⟨i', t'⟩ hit' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_singerD,
      Finset.mem_range] at hit hit'
    simp only at h
    have hlt : ∀ i t, i < q ^ 2 + q + 1 → t < q - 1 →
        i + (q ^ 2 + q + 1) * t < q ^ 3 - 1 := by
      intro i t hi ht
      rw [hN]
      have : (q ^ 2 + q + 1) * (t + 1) ≤ (q ^ 2 + q + 1) * (q - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      nlinarith
    have e := hg.pow_inj (hlt i t hit.1.1 hit.2) (hlt i' t' hit'.1.1 hit'.2) h
    have h1 : i = i' := by
      have := congrArg (· % (q ^ 2 + q + 1)) e
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hit.1.1,
        Nat.mod_eq_of_lt hit'.1.1] at this
      exact this
    subst h1
    have : t = t' := Nat.eq_of_mul_eq_mul_left hn (by omega)
    rw [this]
  have hc := congrArg Finset.card himg
  rw [Finset.card_erase_of_mem hL0, hLcard, Finset.card_image_of_injOn hinj,
    Finset.card_product, Finset.card_range] at hc
  have h2 : q * q - 1 = (q + 1) * (q - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    apply Nat.sub_eq_of_eq_add; ring
  rw [h2] at hc
  exact (Nat.eq_of_mul_eq_mul_right (by omega : 0 < q - 1) hc).symm

lemma singer_inj [Fintype K] [DecidableEq K] {q : ℕ} {g : K} (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 3) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) {a b a' b' : ℕ} (ha : a ∈ singerD q g)
    (hb : b ∈ singerD q g) (ha' : a' ∈ singerD q g) (hb' : b' ∈ singerD q g) (hab : a ≠ b)
    (hmod : a + b' ≡ a' + b [MOD q ^ 2 + q + 1]) : a = a' ∧ b = b' := by
  rw [mem_singerD] at ha hb ha' hb'
  have hN : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := cube_sub_one (by omega)
  have hnN : q ^ 2 + q + 1 ≤ q ^ 3 - 1 := by
    rw [hN]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hg0 := gen_ne_zero hq hg
  have hcv : g ^ (a' + (q ^ 3 - 1) - a) * g ^ a = g ^ a' := by
    rw [← pow_add, Nat.sub_add_cancel (by omega), pow_add, hg.pow_eq_one, mul_one]
  have hx : (a' + (q ^ 3 - 1) - a + b) % (q ^ 2 + q + 1) = b' := by
    have h1 : (a' + (q ^ 3 - 1) - a + b) + a = (a' + b) + (q ^ 2 + q + 1) * (q - 1) := by
      omega
    have h2 : (a' + (q ^ 3 - 1) - a + b) ≡ b' [MOD q ^ 2 + q + 1] := by
      apply Nat.ModEq.add_right_cancel' a
      rw [h1]
      calc a' + b + (q ^ 2 + q + 1) * (q - 1) ≡ a' + b [MOD q ^ 2 + q + 1] :=
            Nat.add_mul_mod_self_left _ _ _
        _ ≡ a + b' [MOD q ^ 2 + q + 1] := hmod.symm
        _ = b' + a := add_comm _ _
    rw [h2]; exact Nat.mod_eq_of_lt hb'.1
  have hcu : g ^ (a' + (q ^ 3 - 1) - a) * g ^ b =
      g ^ ((q ^ 2 + q + 1) * ((a' + (q ^ 3 - 1) - a + b) / (q ^ 2 + q + 1))) * g ^ b' := by
    rw [← pow_add, ← pow_add]; congr 1
    have := Nat.mod_add_div (a' + (q ^ 3 - 1) - a + b) (q ^ 2 + q + 1)
    rw [hx] at this; omega
  have hu0 : g ^ b ≠ 0 := pow_ne_zero _ hg0
  have hind := indep_of (by omega) hadd hu0 (indep_gpow hq hK hg ha.1 hb.1 hab)
  have hspan := pspan_eq hq hK hg hadd hb.2 ha.2 hind
  have hmem1 : g ^ (a' + (q ^ 3 - 1) - a) * g ^ b ∈ pspan q (g ^ b) (g ^ a) := by
    rw [hspan, hcu]; exact smul_mem_pspan ((gpow_fix_iff hq hg _).mpr (dvd_mul_right _ _)) hb'.2
  have hmem2 : g ^ (a' + (q ^ 3 - 1) - a) * g ^ a ∈ pspan q (g ^ b) (g ^ a) := by
    rw [hspan, hcv]; exact ha'.2
  obtain ⟨α, β, hα, hβ, e1⟩ := mem_pspan.mp hmem1
  obtain ⟨γ, δ, hγ, hδ, e2⟩ := mem_pspan.mp hmem2
  have hcfix := core_fix (by omega) hK hadd hα hβ hγ hδ hu0 e1.symm e2.symm
  rw [gpow_fix_iff hq hg] at hcfix
  obtain ⟨m, hm⟩ := hcfix
  have haa : a = a' := by
    have h1 : a' + (q ^ 2 + q + 1) * (q - 1) = a + (q ^ 2 + q + 1) * m := by omega
    have := congrArg (· % (q ^ 2 + q + 1)) h1
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt ha'.1] at this
    exact this.symm
  subst haa
  refine ⟨rfl, ?_⟩
  have := Nat.ModEq.add_left_cancel' a hmod
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb'.1, eq_comm] at this

theorem singer_of_field [Fintype K] [DecidableEq K] {q : ℕ} {g : K} (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 3) (hadd : ∀ x y : K, (x + y) ^ q = x ^ q + y ^ q)
    (hg : IsPrimitiveRoot g (q ^ 3 - 1)) :
    ∃ B : Set ℕ, IsPerfectDifferenceSet B (q ^ 2 + q + 1) ∧ B.ncard = q + 1 := by
  have : NeZero (q ^ 2 + q + 1) := ⟨by positivity⟩
  have hcard := card_singerD hq hK hadd hg
  let f : ℕ × ℕ → ZMod (q ^ 2 + q + 1) := fun p => (p.1 : ZMod (q ^ 2 + q + 1)) - p.2
  have hmaps : Set.MapsTo f ↑(singerD q g).offDiag
      ↑(Finset.univ.filter (fun x : ZMod (q ^ 2 + q + 1) => x ≠ 0)) := by
    rintro ⟨a, b⟩ hab
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe, mem_singerD] at hab
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, f, sub_ne_zero]
    intro h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hab.1.1, Nat.mod_eq_of_lt hab.2.1.1] at h
    exact hab.2.2 h
  have hinj : Set.InjOn f ↑(singerD q g).offDiag := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe] at hab hab'
    simp only [f] at h
    have hmod : a + b' ≡ a' + b [MOD q ^ 2 + q + 1] := by
      rw [← ZMod.natCast_eq_natCast_iff]; push_cast; linear_combination h
    obtain ⟨h1, h2⟩ := singer_inj hq hK hadd hg hab.1 hab.2.1 hab'.1 hab'.2.1 hab.2.2 hmod
    rw [h1, h2]
  have hle : (Finset.univ.filter (fun x : ZMod (q ^ 2 + q + 1) => x ≠ 0)).card ≤
      ((singerD q g).offDiag).card := by
    rw [Finset.offDiag_card, hcard, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
    have : (q + 1) * (q + 1) = q ^ 2 + q + 1 + q := by ring
    omega
  have hsurj := Finset.surjOn_of_injOn_of_card_le f hmaps hinj hle
  refine ⟨↑(singerD q g), ?_, by rw [Set.ncard_coe_finset, hcard]⟩
  unfold IsPerfectDifferenceSet
  rw [← Finset.coe_offDiag]
  have hbij : Set.BijOn f ↑(singerD q g).offDiag
      ↑(Finset.univ.filter (fun x : ZMod (q ^ 2 + q + 1) => x ≠ 0)) := ⟨hmaps, hinj, hsurj⟩
  simpa [f] using hbij

end SingerAux

open SingerAux in
theorem erdos_707.variants.singer_construction (p : ℕ) (hp : IsPrimePow p) :
    ∃ (B : Set ℕ), IsPerfectDifferenceSet B (p^2 + p + 1) ∧ B.ncard = p + 1 := by
  classical
  obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff p).mp hp
  have : Fact r.Prime := ⟨hr⟩
  let : Fintype (GaloisField r (3 * k)) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField r (3 * k)) = (r ^ k) ^ 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card r (3 * k) (by omega), ← pow_mul, mul_comm]
  have hadd : ∀ x y : GaloisField r (3 * k), (x + y) ^ (r ^ k) = x ^ (r ^ k) + y ^ (r ^ k) :=
    fun x y => add_pow_char_pow x y r k
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField r (3 * k))ˣ)
  have hg' : IsPrimitiveRoot (g : GaloisField r (3 * k)) ((r ^ k) ^ 3 - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff]
    have := IsPrimitiveRoot.orderOf g
    rwa [hg, Nat.card_units, Nat.card_eq_fintype_card, hK] at this
  exact singer_of_field hp.two_le hK hadd hg'


end OpenProofs.Erdos707
