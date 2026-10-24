import FormalConjectures.Wikipedia.PollocksConjecture

/-!
# `PollocksConjecture.pollock_tetrahedral.ncard_exceptions`

Upstream: `PollocksConjecture.pollock_tetrahedral.ncard_exceptions` (category textbook), `FormalConjectures/Wikipedia/PollocksConjecture.lean` line 74.

Proof idea: both sides are equivalent to `NotSumOfFourTetrahedral = E` for an explicit list `E`
of 241 numbers, all `≤ 343867`. The kernel computes the bitset of all sums of four tetrahedral
numbers `T a` with `a < 127` (iterated shift-or on a big natural number) and checks that below
`343868` its zero bits are exactly `E`. Since `T 127 > 343867`, a number `n ≤ 343867` is a sum
of four tetrahedral numbers iff it is one with all indices `< 127`, so
`NotSumOfFourTetrahedral ∩ [0, 343867] = E`. If `343867` is the greatest exception, the set is
`E`, of cardinality 241. If the set has cardinality 241, it is finite and contains `E`, which
already has 241 elements, so it equals `E`, whose greatest element is `343867`.
-/

open scoped BigOperators
open PollocksConjecture

namespace OpenProofs.PollocksConjecture

/-- Tetrahedral numbers `T 0, …, T 126` (all those below `343868`). -/
def pollockTets : List ℕ := (List.range 127).map tetrahedral

/-- One step of the sumset bitset: bit `n` of the result is set iff `n = t + m` with
`t ∈ pollockTets` and bit `m` of `B` set. -/
def pollockStep (B : ℕ) : ℕ := pollockTets.foldl (fun acc t => acc ||| (B <<< t)) 0

/-- Bitset of sums of four tetrahedral numbers `T a` with `a < 127`. -/
def pollockB4 : ℕ := pollockStep (pollockStep (pollockStep (pollockStep 1)))

/-- The 241 numbers that are not a sum of four tetrahedral numbers. -/
def pollockExc : List ℕ := [17, 27, 33, 52, 73, 82, 83, 103, 107, 137, 153, 162, 217, 219, 227, 237, 247, 258, 268, 271, 282, 283, 302, 303, 313, 358, 383, 432, 437, 443, 447, 502, 548, 557, 558, 647, 662, 667, 709, 713, 718, 722, 842, 863, 898, 953, 1007, 1117, 1118, 1153, 1227, 1233, 1243, 1314, 1382, 1402, 1468, 1478, 1513, 1523, 1578, 1612, 1622, 1658, 1678, 1693, 1731, 1738, 1742, 1758, 1767, 1803, 1858, 1907, 1923, 1933, 2037, 2053, 2172, 2198, 2217, 2218, 2251, 2253, 2327, 2372, 2382, 2417, 2437, 2457, 2537, 2538, 2578, 2687, 2818, 2858, 2898, 2973, 3138, 3142, 3183, 3218, 3263, 3463, 3512, 3887, 4003, 4307, 4317, 4563, 4832, 4923, 5013, 5142, 5238, 5283, 5483, 5508, 5538, 5563, 5618, 5647, 5707, 6022, 6057, 6067, 6186, 6213, 6263, 6343, 6462, 6863, 7067, 7278, 7377, 7387, 7423, 7497, 7542, 7662, 7793, 7873, 8223, 8307, 8322, 8973, 9063, 9488, 9687, 9753, 9772, 9973, 10397, 10467, 10532, 10633, 10852, 11237, 11302, 11737, 11962, 12247, 12547, 12722, 12777, 12843, 12858, 13127, 13393, 13822, 14492, 15122, 15483, 15867, 16097, 16538, 16637, 16742, 17253, 17683, 17813, 17893, 18573, 18782, 19168, 19277, 20918, 21523, 22618, 22657, 23677, 24237, 24317, 24338, 25447, 25723, 26007, 27858, 28617, 28847, 29157, 29487, 29938, 30298, 31973, 33183, 36262, 36913, 37798, 38453, 38707, 38807, 39693, 39913, 41278, 41322, 41433, 44833, 47627, 48043, 56467, 56842, 58613, 59077, 62158, 64752, 65253, 65567, 71157, 74687, 78003, 78787, 83603, 84023, 85993, 91128, 106277, 113062, 134038, 148437, 343867]

/-- Bitset of `pollockExc`. -/
def pollockExcBits : ℕ := pollockExc.foldl (fun acc e => acc ||| 2 ^ e) 0

theorem pollockB4_eq :
    pollockB4 &&& (2 ^ 343868 - 1) = (2 ^ 343868 - 1) ^^^ pollockExcBits := by
  decide +kernel

theorem pollockExc_le : ∀ e ∈ pollockExc, e ≤ 343867 := by decide +kernel

theorem pollockExc_mem : 343867 ∈ pollockExc := by decide +kernel

theorem pollockExc_nodup : pollockExc.Nodup := by decide +kernel

theorem pollockExc_length : pollockExc.length = 241 := by decide +kernel

theorem pollock_testBit_foldl_shift (B n : ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    (l.foldl (fun acc t => acc ||| (B <<< t)) acc).testBit n = true ↔
      acc.testBit n = true ∨ ∃ t ∈ l, t ≤ n ∧ B.testBit (n - t) = true := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons t l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | ⟨h1, h2⟩) | ⟨s, hs, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, Or.inl rfl, h1, h2⟩
      · exact Or.inr ⟨s, Or.inr hs, h⟩
    · rintro (h | ⟨s, (rfl | hs), h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨s, hs, h⟩

theorem pollock_testBit_step (B n : ℕ) :
    (pollockStep B).testBit n = true ↔
      ∃ a, a < 127 ∧ tetrahedral a ≤ n ∧ B.testBit (n - tetrahedral a) = true := by
  rw [pollockStep, pollock_testBit_foldl_shift]
  simp [pollockTets]

theorem pollock_testBit_one (m : ℕ) : (1 : ℕ).testBit m = true ↔ m = 0 := by
  rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
  simp [eq_comm]

theorem pollock_testBit_B4 (n : ℕ) :
    pollockB4.testBit n = true ↔ ∃ a b c d, a < 127 ∧ b < 127 ∧ c < 127 ∧ d < 127 ∧
      n = tetrahedral a + tetrahedral b + tetrahedral c + tetrahedral d := by
  simp only [pollockB4, pollock_testBit_step, pollock_testBit_one]
  constructor
  · rintro ⟨a, ha, h1, b, hb, h2, c, hc, h3, d, hd, h4, h5⟩
    exact ⟨a, b, c, d, ha, hb, hc, hd, by omega⟩
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, h⟩
    exact ⟨a, ha, by omega, b, hb, by omega, c, hc, by omega, d, hd, by omega, by omega⟩

theorem pollock_tetrahedral_mono {a b : ℕ} (h : a ≤ b) : tetrahedral a ≤ tetrahedral b := by
  unfold tetrahedral
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul (Nat.mul_le_mul h (by omega)) (by omega)

theorem pollock_lt_of_tetrahedral_le {a : ℕ} (h : tetrahedral a ≤ 343867) : a < 127 := by
  by_contra h'
  have h1 := pollock_tetrahedral_mono (show 127 ≤ a by omega)
  have h2 : tetrahedral 127 = 349504 := by decide
  omega

theorem pollock_mem_iff_testBit {n : ℕ} (hn : n ≤ 343867) :
    n ∈ NotSumOfFourTetrahedral ↔ ¬ pollockB4.testBit n = true := by
  rw [pollock_testBit_B4]
  simp only [NotSumOfFourTetrahedral, Set.mem_ofPred_eq]
  constructor
  · rintro h ⟨a, b, c, d, -, -, -, -, h'⟩
    apply h ![a, b, c, d]
    simp [Fin.sum_univ_four, h']
  · rintro h f hf
    rw [Fin.sum_univ_four] at hf
    exact h ⟨f 0, f 1, f 2, f 3, pollock_lt_of_tetrahedral_le (by omega),
      pollock_lt_of_tetrahedral_le (by omega), pollock_lt_of_tetrahedral_le (by omega),
      pollock_lt_of_tetrahedral_le (by omega), hf⟩

theorem pollock_testBit_foldl_pow (n : ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    (l.foldl (fun acc e => acc ||| 2 ^ e) acc).testBit n = true ↔
      acc.testBit n = true ∨ n ∈ l := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons e l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro ((h | rfl) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr h

theorem pollock_mem_iff {n : ℕ} (hn : n ≤ 343867) :
    n ∈ NotSumOfFourTetrahedral ↔ n ∈ pollockExc := by
  rw [pollock_mem_iff_testBit hn]
  have h := congrArg (fun x => x.testBit n) pollockB4_eq
  simp only [Nat.testBit_land, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    show n < 343868 by omega, decide_true, Bool.and_true, Bool.true_xor] at h
  have h2 : pollockExcBits.testBit n = true ↔ n ∈ pollockExc := by
    have := pollock_testBit_foldl_pow n pollockExc 0
    simpa [pollockExcBits] using this
  rw [h, ← h2]
  simp

theorem pollock_eq_of_le (h : ∀ n ∈ NotSumOfFourTetrahedral, n ≤ 343867) :
    NotSumOfFourTetrahedral = (pollockExc.toFinset : Set ℕ) := by
  ext n
  simp only [Finset.mem_coe, List.mem_toFinset]
  constructor
  · intro hn
    exact (pollock_mem_iff (h n hn)).1 hn
  · intro hn
    exact (pollock_mem_iff (pollockExc_le n hn)).2 hn

theorem pollock_card : pollockExc.toFinset.card = 241 := by
  rw [List.toFinset_card_of_nodup pollockExc_nodup, pollockExc_length]

theorem pollock_tetrahedral.ncard_exceptions :
    type_of% pollock_tetrahedral.salzer_levine ↔
    NotSumOfFourTetrahedral.ncard = 241 := by
  constructor
  · intro h
    rw [pollock_eq_of_le (fun n hn => h.2 hn), Set.ncard_coe_finset, pollock_card]
  · intro h
    have hfin : NotSumOfFourTetrahedral.Finite := Set.finite_of_ncard_ne_zero (by omega)
    have hsub : (pollockExc.toFinset : Set ℕ) ⊆ NotSumOfFourTetrahedral := by
      intro n hn
      simp only [Finset.mem_coe, List.mem_toFinset] at hn
      exact (pollock_mem_iff (pollockExc_le n hn)).2 hn
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (by rw [h, Set.ncard_coe_finset, pollock_card]) hfin
    rw [← heq]
    refine ⟨?_, ?_⟩
    · simpa using pollockExc_mem
    · intro n hn
      simp only [Finset.mem_coe, List.mem_toFinset] at hn
      exact pollockExc_le n hn

end OpenProofs.PollocksConjecture
