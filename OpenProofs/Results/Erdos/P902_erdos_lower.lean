import FormalConjectures.ErdosProblems.«902»

/-!
# Erdős 902: `erdos_902.variants.erdos_lower`

Upstream: `Erdos902.erdos_902.variants.erdos_lower`. Since `f n` is an `sInf` over `ℕ`, the
bound needs two facts. (1) Every `m` in the defining set satisfies `2 ^ (n + 1) - 1 ≤ m`, by
induction on `n` (Erdős's argument): in a tournament with property `S_(n+1)`, the
in-neighbourhood `I(v)` of any vertex `v` has at least `n + 1` elements (otherwise a superset
of `insert v I(v)` of size `n + 1` would be dominated by a vertex beating `v`, which lies in
`I(v)`), and as a sub-tournament it has property `S_n` (dominate `E ∪ {v}`). So every in-degree
is at least `2 ^ (n + 1) - 1`, and `2 * ∑ indeg + m ≤ m * m` gives `m ≥ 2 ^ (n + 2) - 1`.
(2) The set is nonempty, which needs the existence of tournaments with property `S_n`: for
`n = 0` take one vertex; for `n ≥ 1` this is Erdős's counting argument, done on Boolean
matrices `σ` with `x → y ↔ x ≠ y ∧ σ x y ⊕ σ y x ⊕ (x < y)`. For a fixed `n`-set `E`, flipping
the entries `(x, e)`, `x ∉ E`, `e ∈ E`, is an involution turning "`E` is not dominated" into a
product condition on rows, so at most `(2 ^ N) ^ n * (2 ^ N - 2 ^ (N - n)) ^ (N - n)` matrices
leave `E` undominated; with `N = n + (2 ^ n - 1) * 2 ^ (2 * n + 2)`, Bernoulli's inequality and
`choose N n ≤ N ^ n` show the union bound over all `n`-sets is below `(2 ^ N) ^ N`.
-/

open Erdos902

namespace OpenProofs.Erdos902

theorem lower_two_mul_sum_indeg_add_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj] (hG : G.IsTournament) :
    2 * (∑ v : V, ∑ x, if G.Adj x v then 1 else 0) + Fintype.card V ≤
      Fintype.card V * Fintype.card V := by
  set m := Fintype.card V with hm
  have hpt : ∀ v x : V, ((if G.Adj x v then 1 else 0) + (if G.Adj v x then 1 else 0) +
      (if x = v then 1 else 0) : ℕ) ≤ 1 := by
    intro v x
    by_cases hxv : x = v
    · subst hxv
      simp [hG.1]
    · have := hG.2 x v hxv
      by_cases h : G.Adj x v <;> simp_all
  have hdeg : ∀ v : V, (∑ x, if G.Adj x v then 1 else 0) +
      (∑ x, if G.Adj v x then 1 else 0) + 1 ≤ m := by
    intro v
    calc (∑ x, if G.Adj x v then 1 else 0) + (∑ x, if G.Adj v x then 1 else 0) + 1
        = ∑ x, ((if G.Adj x v then 1 else 0) + (if G.Adj v x then 1 else 0) +
            (if x = v then 1 else 0) : ℕ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
      _ ≤ ∑ _x : V, 1 := Finset.sum_le_sum fun x _ => hpt v x
      _ = m := by simp [hm]
  have hsum : ∑ v : V, ((∑ x, if G.Adj x v then 1 else 0) +
      (∑ x, if G.Adj v x then 1 else 0) + 1) ≤ m * m := by
    calc _ ≤ ∑ _v : V, m := Finset.sum_le_sum fun v _ => hdeg v
      _ = m * m := by simp [hm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_comm (f := fun v x => if G.Adj v x then 1 else 0)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  omega

theorem lower_indeg_mem {m n : ℕ} (G : Digraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.IsTournament) (hS : HasPropertyS G (n + 1)) (hm : n + 1 ≤ m) (v : Fin m) :
    n ≤ (Finset.univ.filter fun x => G.Adj x v).card ∧
      ∃ G' : Digraph (Fin (Finset.univ.filter fun x => G.Adj x v).card),
        G'.IsTournament ∧ HasPropertyS G' n := by
  set I := Finset.univ.filter fun x => G.Adj x v with hI
  have hvI : v ∉ I := by simp [hI, hG.1 v]
  constructor
  · by_contra hlt
    have hcard : (insert v I).card ≤ n + 1 := by
      rw [Finset.card_insert_of_notMem hvI]
      omega
    obtain ⟨F, hF, hFcard⟩ := Finset.exists_superset_card_eq hcard (by simpa using hm)
    obtain ⟨x, hxF, hx⟩ := hS F hFcard
    have hxv : G.Adj x v := hx v (hF (Finset.mem_insert_self _ _))
    exact hxF (hF (Finset.mem_insert_of_mem (by simp [hI, hxv])))
  · let e : Fin I.card ≃ I := I.equivFin.symm
    refine ⟨⟨fun i j => G.Adj (e i) (e j)⟩, ⟨fun i => hG.1 _, fun i j hij => hG.2 _ _ ?_⟩, ?_⟩
    · intro h
      exact hij (e.injective (Subtype.ext h))
    · intro E' hE'
      let emb : Fin I.card ↪ Fin m := e.toEmbedding.trans (Function.Embedding.subtype _)
      have hemb : ∀ i, emb i ∈ I := fun i => (e i).2
      have hvE : v ∉ E'.map emb := by
        rw [Finset.mem_map]
        rintro ⟨i, -, hi⟩
        exact hvI (hi ▸ hemb i)
      obtain ⟨x, hxE, hx⟩ := hS (insert v (E'.map emb))
        (by rw [Finset.card_insert_of_notMem hvE, Finset.card_map, hE'])
      have hxI : x ∈ I := by
        simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx v (Finset.mem_insert_self _ _)
      refine ⟨e.symm ⟨x, hxI⟩, ?_, ?_⟩
      · intro hmem
        apply hxE
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_map]
        exact ⟨_, hmem, by simp [emb]⟩
      · intro j hj
        show G.Adj (e (e.symm ⟨x, hxI⟩)) (e j)
        rw [Equiv.apply_symm_apply]
        exact hx _ (Finset.mem_insert_of_mem (Finset.mem_map_of_mem emb hj))

theorem lower_bound_of_mem (n : ℕ) : ∀ m ∈ {m : ℕ | n ≤ m ∧
    ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}, 2 ^ (n + 1) - 1 ≤ m := by
  induction n with
  | zero =>
    rintro m ⟨-, G, -, hS⟩
    obtain ⟨x, -, -⟩ := hS ∅ rfl
    have := x.pos
    norm_num
    omega
  | succ n ih =>
    rintro m ⟨hm, G, hG, hS⟩
    classical
    have hdeg : ∀ v, 2 ^ (n + 1) - 1 ≤ ∑ x, if G.Adj x v then 1 else 0 := by
      intro v
      rw [← Finset.card_filter]
      exact ih _ (lower_indeg_mem G hG hS hm v)
    have hsum := lower_two_mul_sum_indeg_add_card_le G hG
    simp only [Fintype.card_fin] at hsum
    have hlow : m * (2 ^ (n + 1) - 1) ≤ ∑ v : Fin m, ∑ x, if G.Adj x v then 1 else 0 := by
      calc m * (2 ^ (n + 1) - 1) = ∑ _v : Fin m, (2 ^ (n + 1) - 1) := by simp
        _ ≤ _ := Finset.sum_le_sum fun v _ => hdeg v
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ (n + 1) = b + 1 := ⟨2 ^ (n + 1) - 1, by
      have := Nat.one_le_two_pow (n := n + 1); omega⟩
    have h2 : 2 ^ (n + 1 + 1) - 1 = 2 * b + 1 := by rw [pow_succ, hb]; omega
    rw [hb, Nat.add_sub_cancel] at hlow
    rw [h2]
    have hm0 : 0 < m := by omega
    have : m * (2 * b + 1) ≤ m * m := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hm0


/-- The tournament on `Fin N` encoded by a Boolean matrix. -/
def lowerBoolTournament {N : ℕ} (σ : Fin N → Fin N → Bool) : Digraph (Fin N) where
  Adj x y := x ≠ y ∧ xor (xor (σ x y) (σ y x)) (decide (x < y)) = true

instance lowerBoolTournament_decidableRel {N : ℕ} (σ : Fin N → Fin N → Bool) :
    DecidableRel (lowerBoolTournament σ).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ _))

theorem lowerBoolTournament_isTournament {N : ℕ} (σ : Fin N → Fin N → Bool) :
    (lowerBoolTournament σ).IsTournament := by
  refine ⟨fun v h => h.1 rfl, fun u v huv => ?_⟩
  simp only [lowerBoolTournament]
  rcases lt_or_gt_of_ne huv with h | h
  · have h' : ¬ v < u := not_lt.2 h.le
    simp only [h, h', decide_true, decide_false, ne_eq, huv, not_false_eq_true, true_and,
      Ne.symm huv]
    cases σ u v <;> cases σ v u <;> simp
  · have h' : ¬ u < v := not_lt.2 h.le
    simp only [h, h', decide_true, decide_false, ne_eq, huv, not_false_eq_true, true_and,
      Ne.symm huv]
    cases σ u v <;> cases σ v u <;> simp

/-- Flip the entries `(x, e)`, `x ∉ E`, `e ∈ E`, so that `x → e` becomes `τ x e = true`. -/
def lowerFlip {N : ℕ} (E : Finset (Fin N)) (σ : Fin N → Fin N → Bool) : Fin N → Fin N → Bool :=
  fun x y => if x ∉ E ∧ y ∈ E then xor (xor (σ x y) (σ y x)) (decide (x < y)) else σ x y

theorem lowerFlip_involutive {N : ℕ} (E : Finset (Fin N)) (σ : Fin N → Fin N → Bool) :
    lowerFlip E (lowerFlip E σ) = σ := by
  funext x y
  by_cases h : x ∉ E ∧ y ∈ E
  · simp only [lowerFlip, h]
    cases σ x y <;> cases σ y x <;> cases decide (x < y) <;> rfl
  · simp only [lowerFlip, h, if_false]

theorem lowerFlip_adj {N : ℕ} (E : Finset (Fin N)) (σ : Fin N → Fin N → Bool) {x e : Fin N}
    (hx : x ∉ E) (he : e ∈ E) : (lowerBoolTournament σ).Adj x e ↔ lowerFlip E σ x e = true := by
  have hxe : x ≠ e := fun h => hx (h ▸ he)
  simp [lowerBoolTournament, lowerFlip, hx, he, hxe]

theorem lowerRowCount {N : ℕ} (E : Finset (Fin N)) :
    (Finset.univ.filter fun r : Fin N → Bool => ∀ e ∈ E, r e = true).card = 2 ^ (N - E.card) := by
  have : (Finset.univ.filter fun r : Fin N → Bool => ∀ e ∈ E, r e = true) =
      Fintype.piFinset fun i => if i ∈ E then {true} else Finset.univ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · simp [h i hi]
      · simp
    · intro h e he
      simpa [he] using h e
  rw [this, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, Fintype.card_bool]
  rw [Finset.prod_ite]
  simp [Finset.filter_not, Finset.card_sdiff]

theorem lowerBad_card_le {N : ℕ} (E : Finset (Fin N)) :
    (Finset.univ.filter fun σ : Fin N → Fin N → Bool =>
        ∀ x, x ∉ E → ¬ ∀ e ∈ E, (lowerBoolTournament σ).Adj x e).card ≤
      (2 ^ N) ^ E.card * (2 ^ N - 2 ^ (N - E.card)) ^ (N - E.card) := by
  set R := Finset.univ.filter fun r : Fin N → Bool => ¬ ∀ e ∈ E, r e = true with hR
  have hRcard : R.card = 2 ^ N - 2 ^ (N - E.card) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N → Bool))) (fun r : Fin N → Bool => ∀ e ∈ E, r e = true)
    rw [lowerRowCount] at h
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
    rw [hR]
    omega
  calc _ ≤ (Fintype.piFinset fun x => if x ∈ E then Finset.univ else R).card := by
        refine Finset.card_le_card_of_injOn (lowerFlip E) ?_ ?_
        · intro σ hσ
          rw [Finset.mem_coe, Finset.mem_filter] at hσ
          rw [Finset.mem_coe, Fintype.mem_piFinset]
          intro x
          split_ifs with hx
          · exact Finset.mem_univ _
          · rw [hR, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun hall => ?_⟩
            replace hσ := hσ.2
            exact hσ x hx fun e he => (lowerFlip_adj E σ hx he).2 (hall e he)
        · intro σ₁ _ σ₂ _ h
          have := congrArg (lowerFlip E) h
          rwa [lowerFlip_involutive, lowerFlip_involutive] at this
    _ = (2 ^ N) ^ E.card * R.card ^ (N - E.card) := by
        rw [Fintype.card_piFinset]
        simp only [apply_ite Finset.card, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
        rw [Finset.prod_ite]
        simp [Finset.filter_not, Finset.card_sdiff]
    _ = _ := by rw [hRcard]

theorem lower_bernoulli (p m : ℕ) : p ^ m * (p + m) ≤ p * (p + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have heq : p ^ (m + 1) * (p + (m + 1)) + p ^ m * m = (p + 1) * (p ^ m * (p + m)) := by ring
    calc p ^ (m + 1) * (p + (m + 1)) ≤ (p + 1) * (p ^ m * (p + m)) := by omega
      _ ≤ (p + 1) * (p * (p + 1) ^ m) := Nat.mul_le_mul_left _ ih
      _ = p * (p + 1) ^ (m + 1) := by ring

theorem lower_numeric (n N : ℕ) (hn : 0 < n) (hN : N = n + (2 ^ n - 1) * 2 ^ (2 * n + 2)) :
    N.choose n * ((2 ^ N) ^ n * (2 ^ N - 2 ^ (N - n)) ^ (N - n)) < (2 ^ N) ^ N := by
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set p := 2 ^ n - 1 with hp
  set t := 2 ^ (2 * n + 2) with ht
  set k := N - n with hk
  have hq : 2 ^ n = p + 1 := by omega
  have hp1 : 1 ≤ p := by omega
  have hkpt : k = p * t := by omega
  have hNnk : N = n + k := by omega
  have hA : 2 ^ N = 2 ^ k * (p + 1) := by rw [← hq, ← pow_add]; congr 1; omega
  have hAB : 2 ^ N - 2 ^ k = 2 ^ k * p := by
    rw [hA, Nat.mul_add, mul_one, Nat.add_sub_cancel]
  -- `N ^ n < 2 ^ t`
  have hnt : n ≤ t := by
    have := n.lt_two_pow_self
    have : 2 ^ n ≤ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hNle : N ≤ 2 ^ (3 * n + 2) := by
    have : 2 ^ (3 * n + 2) = (p + 1) * t := by rw [← hq, ht, ← pow_add]; congr 1; ring
    rw [this]
    nlinarith
  have hexp : (3 * n + 2) * n < t := by
    have h1 := n.lt_two_pow_self
    have : t = 4 * (2 ^ n) ^ 2 := by rw [ht, ← pow_mul]; ring
    rw [this]
    nlinarith
  have hNpow : N ^ n < 2 ^ t := by
    calc N ^ n ≤ (2 ^ (3 * n + 2)) ^ n := Nat.pow_le_pow_left hNle n
      _ = 2 ^ ((3 * n + 2) * n) := by rw [← pow_mul]
      _ < 2 ^ t := Nat.pow_lt_pow_right (by norm_num) hexp
  have hC : N.choose n < 2 ^ t := lt_of_le_of_lt (Nat.choose_le_pow N n) hNpow
  -- Bernoulli: `2 ^ t * p ^ k ≤ (p + 1) ^ k`
  have hB1 : 2 * p ^ p ≤ (p + 1) ^ p := by
    have := lower_bernoulli p p
    have h' : p * (2 * p ^ p) ≤ p * (p + 1) ^ p := by nlinarith
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  have hB : 2 ^ t * p ^ k ≤ (p + 1) ^ k := by
    have := Nat.pow_le_pow_left hB1 t
    rw [hkpt, pow_mul, pow_mul, ← mul_pow]
    exact this
  have hpk : 0 < p ^ k := by positivity
  have hcore : N.choose n * p ^ k < (p + 1) ^ k :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hC hpk) hB
  rw [hAB, hA, hNnk]
  have hpos : 0 < (2 ^ k * (p + 1)) ^ n * (2 ^ k) ^ k := by positivity
  calc (n + k).choose n * ((2 ^ k * (p + 1)) ^ n * (2 ^ k * p) ^ k)
      = (2 ^ k * (p + 1)) ^ n * (2 ^ k) ^ k * ((n + k).choose n * p ^ k) := by ring
    _ < (2 ^ k * (p + 1)) ^ n * (2 ^ k) ^ k * (p + 1) ^ k :=
        Nat.mul_lt_mul_of_pos_left (hNnk ▸ hcore) hpos
    _ = (2 ^ k * (p + 1)) ^ n * (2 ^ k * (p + 1)) ^ k := by
        rw [mul_pow (2 ^ k) (p + 1) k]
        ring
    _ = (2 ^ k * (p + 1)) ^ (n + k) := (pow_add _ _ _).symm


theorem lower_exists_propertyS (n : ℕ) :
    ∃ m, n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, Nat.zero_le _, ⟨fun _ _ => False⟩,
      ⟨fun _ h => h, fun u v huv => absurd (Subsingleton.elim u v) huv⟩, ?_⟩
    intro E hE
    rw [Finset.card_eq_zero] at hE
    subst hE
    exact ⟨0, Finset.notMem_empty _, fun e he => absurd he (Finset.notMem_empty _)⟩
  · set N := n + (2 ^ n - 1) * 2 ^ (2 * n + 2) with hN
    have key := lower_numeric n N hn hN
    by_contra hcon
    have hall : ∀ σ : Fin N → Fin N → Bool,
        ∃ E ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)),
          σ ∈ Finset.univ.filter fun σ : Fin N → Fin N → Bool =>
            ∀ x, x ∉ E → ¬ ∀ e ∈ E, (lowerBoolTournament σ).Adj x e := by
      intro σ
      by_contra hno
      apply hcon
      refine ⟨N, by omega, lowerBoolTournament σ, lowerBoolTournament_isTournament σ, ?_⟩
      intro E hE
      by_contra hx
      apply hno
      refine ⟨E, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hE⟩,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x hxE hP => hx ⟨x, hxE, hP⟩⟩⟩
    have hsub : (Finset.univ : Finset (Fin N → Fin N → Bool)) ⊆
        (Finset.powersetCard n Finset.univ).biUnion fun E =>
          Finset.univ.filter fun σ : Fin N → Fin N → Bool =>
            ∀ x, x ∉ E → ¬ ∀ e ∈ E, (lowerBoolTournament σ).Adj x e := by
      intro σ _
      rw [Finset.mem_biUnion]
      exact hall σ
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ E ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)),
        (Finset.univ.filter fun σ : Fin N → Fin N → Bool =>
          ∀ x, x ∉ E → ¬ ∀ e ∈ E, (lowerBoolTournament σ).Adj x e).card ≤
        ∑ _E ∈ Finset.powersetCard n (Finset.univ : Finset (Fin N)),
          (2 ^ N) ^ n * (2 ^ N - 2 ^ (N - n)) ^ (N - n) := by
      refine Finset.sum_le_sum fun E hE => ?_
      have := lowerBad_card_le E
      rwa [(Finset.mem_powersetCard.1 hE).2] at this
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at h2
    have h3 : (Finset.univ : Finset (Fin N → Fin N → Bool)).card = (2 ^ N) ^ N := by simp
    have h4 := h1.trans h2
    rw [h3] at h4
    exact absurd key (not_lt.2 h4)

theorem erdos_902.variants.erdos_lower (n : ℕ) : 2 ^ (n + 1) - 1 ≤ f n := by
  obtain ⟨m, hm⟩ := lower_exists_propertyS n
  exact le_csInf ⟨m, hm⟩ (lower_bound_of_mem n)

end OpenProofs.Erdos902
