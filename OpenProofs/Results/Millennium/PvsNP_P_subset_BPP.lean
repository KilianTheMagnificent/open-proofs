import FormalConjectures.Millennium.PvsNP

/-!
# `ComplexityTheory.P_subset_BPP`

Upstream: `ComplexityTheory.P_subset_BPP` (category textbook), `FormalConjectures/Millennium/PvsNP.lean` line 106.
Proof idea: take `p = 0` and `R (x, r) = L x`; every random string then agrees with `L x`,
so the acceptance ratio is `1 ≥ 2/3`. The work is showing `R` is polynomial-time, i.e. that
precomposing a polytime machine with `Prod.fst` stays polytime (Mathlib's composition lemma is
only `proof_wanted`). We build the machine explicitly: one extra stack and a scratch register;
it parses the self-delimiting first block of the pair encoding onto the extra stack, discards the
rest of the input, reverses the block back onto the input stack, then runs the original program
lifted to the bigger state space (`stepAux_liftStmt`, `iterate_liftCfg`). Total time is
`n + 2 + time n`, using monotonicity of `Polynomial ℕ` evaluation.
-/

open ComplexityTheory Turing Computability StateTransition

namespace OpenProofs.ComplexityTheory.PSubsetBPPAux

variable (T : FinTM2)

/-- Stack alphabets of the new machine: an extra stack `none` with the input alphabet. -/
abbrev NΓ (o : Option T.K) : Type := T.Γ (o.getD T.k₀)

/-- Labels of the new machine: three preprocessing labels, then the old labels. -/
abbrev NΛ : Type := Option Bool ⊕ T.Λ

/-- States of the new machine: a scratch register and the old state. -/
abbrev Nσ : Type := Option (T.Γ T.k₀) × T.σ

/-- Lift a statement of `T` to the new machine. -/
noncomputable def liftStmt : TM2.Stmt T.Γ T.Λ T.σ → TM2.Stmt (NΓ T) (NΛ T) (Nσ T)
  | .push k f q => .push (some k) (fun s => f s.2) (liftStmt q)
  | .peek k f q => .peek (some k) (fun s a => (s.1, f s.2 a)) (liftStmt q)
  | .pop k f q => .pop (some k) (fun s a => (s.1, f s.2 a)) (liftStmt q)
  | .load a q => .load (fun s => (s.1, a s.2)) (liftStmt q)
  | .branch p q₁ q₂ => .branch (fun s => p s.2) (liftStmt q₁) (liftStmt q₂)
  | .goto l => .goto (fun s => Sum.inr (l s.2))
  | .halt => .halt

variable (ia : T.Γ T.k₀ ≃ Bool)

/-- The program of the new machine. -/
noncomputable def prog : NΛ T → TM2.Stmt (NΓ T) (NΛ T) (Nσ T)
  | .inl none =>
    .pop (some T.k₀) (fun s a => (a, s.2))
      (.branch (fun s => (s.1.map ia).getD false)
        (.pop (some T.k₀) (fun s a => (a, s.2))
          (.push none (fun s => s.1.getD (ia.symm false)) (.goto fun _ => .inl none)))
        (.goto fun _ => .inl (some false)))
  | .inl (some false) =>
    .pop (some T.k₀) (fun s a => (a, s.2))
      (.branch (fun s => s.1.isSome) (.goto fun _ => .inl (some false))
        (.goto fun _ => .inl (some true)))
  | .inl (some true) =>
    .pop none (fun s a => (a, s.2))
      (.branch (fun s => s.1.isSome)
        (.push (some T.k₀) (fun s => s.1.getD (ia.symm false)) (.goto fun _ => .inl (some true)))
        (.goto fun _ => .inr T.main))
  | .inr l => liftStmt T (T.m l)

/-- The new machine. -/
noncomputable abbrev newTM : FinTM2 where
  K := Option T.K
  kDecidableEq := inferInstance
  kFin := by haveI := T.kFin; infer_instance
  k₀ := some T.k₀
  k₁ := some T.k₁
  Γ := NΓ T
  Λ := NΛ T
  main := Sum.inl none
  ΛFin := by haveI := T.ΛFin; infer_instance
  σ := Nσ T
  initialState := (none, T.initialState)
  σFin := by haveI := T.σFin; haveI := T.Γk₀Fin; infer_instance
  Γk₀Fin := T.Γk₀Fin
  m := prog T ia


/-- Lift a stack family of `T`; the extra stack is empty. -/
def liftStk (S : ∀ k, List (T.Γ k)) : ∀ o : Option T.K, List (NΓ T o)
  | none => []
  | some k => S k

/-- Lift a configuration of `T`. -/
noncomputable def liftCfg (c : T.Cfg) : TM2.Cfg (NΓ T) (NΛ T) (Nσ T) :=
  ⟨c.l.map Sum.inr, (none, c.var), liftStk T c.stk⟩

theorem liftStk_update (S : ∀ k, List (T.Γ k)) (k : T.K) (v : List (T.Γ k)) :
    Function.update (liftStk T S) (some k) v = liftStk T (Function.update S k v) := by
  funext o
  cases o with
  | none => rw [Function.update_of_ne (by simp)]; rfl
  | some j =>
    by_cases h : j = k
    · subst h; simp [liftStk]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [liftStk, Function.update_of_ne h]

theorem stepAux_liftStmt (q : TM2.Stmt T.Γ T.Λ T.σ) (v : T.σ) (S : ∀ k, List (T.Γ k)) :
    TM2.stepAux (liftStmt T q) ((none : Option (T.Γ T.k₀)), v) (liftStk T S) =
      liftCfg T (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp only [liftStmt, TM2.stepAux]; rw [← ih]; rw [← liftStk_update]; rfl
  | peek k f q ih => simp only [liftStmt, TM2.stepAux]; rw [← ih]; rfl
  | pop k f q ih => simp only [liftStmt, TM2.stepAux]; rw [← ih]; rw [← liftStk_update]; rfl
  | load a q ih => simp only [liftStmt, TM2.stepAux]; rw [← ih]
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, TM2.stepAux]; rw [ih₁, ih₂]; cases p v <;> rfl
  | goto l => rfl
  | halt => rfl

theorem step_liftCfg (c : T.Cfg) :
    TM2.step (prog T ia) (liftCfg T c) = (T.step c).map (liftCfg T) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · exact congrArg some (stepAux_liftStmt T (T.m l) v S)

theorem iterate_liftCfg (n : ℕ) (c : T.Cfg) :
    (flip bind (TM2.step (prog T ia)))^[n] (some (liftCfg T c)) =
      ((flip bind T.step)^[n] (some c)).map (liftCfg T) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rcases (flip bind T.step)^[n] (some c) with _ | c'
    · rfl
    · simp only [flip, Option.map_some]
      exact step_liftCfg T ia c'

/-- Stacks of the new machine during preprocessing: `A` on the input stack, `B` on the
extra stack, everything else empty. -/
def stk2 (A B : List (T.Γ T.k₀)) : ∀ o : Option T.K, List (NΓ T o)
  | none => B
  | some k => (initList T A).stk k

@[simp] theorem stk2_none (A B : List (T.Γ T.k₀)) : stk2 T A B none = B := rfl

@[simp] theorem stk2_some (A B : List (T.Γ T.k₀)) : stk2 T A B (some T.k₀) = A := by
  simp [stk2, initList]

@[simp] theorem update_stk2_some [DecidableEq (Option T.K)] (A B A' : List (T.Γ T.k₀)) :
    Function.update (stk2 T A B) (some T.k₀) A' = stk2 T A' B := by
  funext o
  cases o with
  | none => rw [Function.update_of_ne (by simp)]; rfl
  | some k =>
    by_cases h : k = T.k₀
    · subst h; rw [Function.update_self, stk2_some]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [stk2, initList, h]

@[simp] theorem update_stk2_none [DecidableEq (Option T.K)] (A B B' : List (T.Γ T.k₀)) :
    Function.update (stk2 T A B) none B' = stk2 T A B' := by
  funext o
  cases o with
  | none => rw [Function.update_self]; rfl
  | some k => rw [Function.update_of_ne (by simp)]; rfl

theorem newTM_step : (newTM T ia).step = TM2.step (prog T ia) := rfl

theorem iter_succ' {α : Type} (f : α → Option α) (n : ℕ) (c : α) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (f c) := by
  rw [Function.iterate_succ_apply]; rfl

theorem step_parse_true (b : Bool) (A B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀)) (v : T.σ) :
    TM2.step (prog T ia) ⟨some (Sum.inl none), (a, v), stk2 T (ia.symm true :: ia.symm b :: A) B⟩ =
      some ⟨some (Sum.inl none), (some (ia.symm b), v), stk2 T A (ia.symm b :: B)⟩ := by
  simp [prog]

theorem step_parse_false (A B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀)) (v : T.σ) :
    TM2.step (prog T ia) ⟨some (Sum.inl none), (a, v), stk2 T (ia.symm false :: A) B⟩ =
      some ⟨some (Sum.inl (some false)), (some (ia.symm false), v), stk2 T A B⟩ := by
  simp [prog]

theorem step_clear_cons (x : T.Γ T.k₀) (A B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀))
    (v : T.σ) :
    TM2.step (prog T ia) ⟨some (Sum.inl (some false)), (a, v), stk2 T (x :: A) B⟩ =
      some ⟨some (Sum.inl (some false)), (some x, v), stk2 T A B⟩ := by
  simp [prog]

theorem step_clear_nil (B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀)) (v : T.σ) :
    TM2.step (prog T ia) ⟨some (Sum.inl (some false)), (a, v), stk2 T [] B⟩ =
      some ⟨some (Sum.inl (some true)), (none, v), stk2 T [] B⟩ := by
  simp [prog]

theorem step_rev_cons (x : T.Γ T.k₀) (A B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀))
    (v : T.σ) :
    TM2.step (prog T ia) ⟨some (Sum.inl (some true)), (a, v), stk2 T A (x :: B)⟩ =
      some ⟨some (Sum.inl (some true)), (some x, v), stk2 T (x :: A) B⟩ := by
  simp [prog]

theorem step_rev_nil (A : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀)) (v : T.σ) :
    TM2.step (prog T ia) ⟨some (Sum.inl (some true)), (a, v), stk2 T A []⟩ =
      some ⟨some (Sum.inr T.main), (none, v), stk2 T A []⟩ := by
  simp [prog]

theorem parse_loop (l rest : List Bool) (B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀))
    (v : T.σ) :
    (flip bind (TM2.step (prog T ia)))^[l.length + 1]
        (some ⟨some (Sum.inl none), (a, v),
          stk2 T ((BitstringEncoding.delimit l ++ rest).map ia.symm) B⟩) =
      some ⟨some (Sum.inl (some false)), (some (ia.symm false), v),
        stk2 T (rest.map ia.symm) ((l.map ia.symm).reverse ++ B)⟩ := by
  induction l generalizing a B with
  | nil =>
    rw [iter_succ']
    exact step_parse_false T ia _ _ _ _
  | cons b l ih =>
    rw [List.length_cons, iter_succ']
    simp only [BitstringEncoding.delimit, List.cons_append, List.map_cons]
    rw [step_parse_true, ih]
    simp

theorem clear_loop (rest : List Bool) (B : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀))
    (v : T.σ) :
    (flip bind (TM2.step (prog T ia)))^[rest.length + 1]
        (some ⟨some (Sum.inl (some false)), (a, v), stk2 T (rest.map ia.symm) B⟩) =
      some ⟨some (Sum.inl (some true)), (none, v), stk2 T [] B⟩ := by
  induction rest generalizing a with
  | nil =>
    rw [iter_succ']
    exact step_clear_nil T ia _ _ _
  | cons b rest ih =>
    rw [List.length_cons, iter_succ', List.map_cons, step_clear_cons, ih]

theorem rev_loop (B A : List (T.Γ T.k₀)) (a : Option (T.Γ T.k₀)) (v : T.σ) :
    (flip bind (TM2.step (prog T ia)))^[B.length + 1]
        (some ⟨some (Sum.inl (some true)), (a, v), stk2 T A B⟩) =
      some ⟨some (Sum.inr T.main), (none, v), stk2 T (B.reverse ++ A) []⟩ := by
  induction B generalizing a A with
  | nil =>
    rw [iter_succ']
    exact step_rev_nil T ia _ _ _
  | cons x B ih =>
    rw [List.length_cons, iter_succ', step_rev_cons, ih]
    simp

theorem initList_newTM (A : List (T.Γ T.k₀)) :
    initList (newTM T ia) A = ⟨some (Sum.inl none), (none, T.initialState), stk2 T A []⟩ := by
  simp only [initList]
  congr 1
  funext o
  cases o with
  | none => simp [stk2]
  | some k =>
    by_cases h : k = T.k₀
    · subst h; simp [stk2, initList]
    · simp [stk2, initList, h]

theorem liftCfg_initList (A : List (T.Γ T.k₀)) :
    liftCfg T (initList T A) = ⟨some (Sum.inr T.main), (none, T.initialState), stk2 T A []⟩ :=
  rfl

theorem liftCfg_haltList (A : List (T.Γ T.k₁)) :
    liftCfg T (haltList T A) = haltList (newTM T ia) A := by
  simp only [liftCfg, haltList]
  congr 1
  funext o
  cases o with
  | none => simp [liftStk]
  | some k =>
    by_cases h : k = T.k₁
    · subst h; simp [liftStk]
    · simp [liftStk, h]

theorem eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- Composing a polynomial-time function with the first projection of a pair stays
polynomial-time. -/
theorem isPolyTime_comp_fst {α γ β : Type} [BitstringEncoding α] [BitstringEncoding γ]
    [BitstringEncoding β] (f : α → β) (hf : IsPolyTime f) :
    IsPolyTime (fun p : α × γ => f p.1) := by
  obtain ⟨M⟩ := hf
  refine ⟨{ tm := newTM M.tm M.inputAlphabet
            inputAlphabet := M.inputAlphabet
            outputAlphabet := M.outputAlphabet
            time := Polynomial.X + 2 + M.time
            outputsFun := fun p => ?_ }⟩
  obtain ⟨a, c⟩ := p
  obtain ⟨⟨s, hs⟩, hsle⟩ := M.outputsFun a
  refine ⟨⟨s + (((BitstringEncoding.bitEncode a).length + 1) +
    (((BitstringEncoding.bitEncode c).length + 1) +
      ((BitstringEncoding.bitEncode a).length + 1))), ?_⟩, ?_⟩
  · change (flip bind (TM2.step (prog M.tm M.inputAlphabet)))^[_]
      (some (initList (newTM M.tm M.inputAlphabet)
        ((BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
          BitstringEncoding.bitEncode c).map M.inputAlphabet.symm))) = _
    rw [initList_newTM, Function.iterate_add_apply _ s,
      Function.iterate_add_apply _ ((BitstringEncoding.bitEncode a).length + 1),
      Function.iterate_add_apply _ ((BitstringEncoding.bitEncode c).length + 1),
      parse_loop, clear_loop, List.append_nil,
      show (BitstringEncoding.bitEncode a).length =
        ((BitstringEncoding.bitEncode a).map M.inputAlphabet.symm).reverse.length by simp,
      rev_loop]
    simp only [List.append_nil, List.reverse_reverse]
    rw [← liftCfg_initList, iterate_liftCfg]
    have hs' : (flip bind M.tm.step)^[s] (some (initList M.tm
        ((BitstringEncoding.bitEncode a).map M.inputAlphabet.symm))) = _ := hs
    rw [hs']
    exact congrArg some (liftCfg_haltList M.tm M.inputAlphabet _)
  · have hmono := eval_mono_nat M.time (a := (BitstringEncoding.bitEncode a).length)
      (b := (BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
        BitstringEncoding.bitEncode c).length) (by simp; omega)
    have hsle' : s ≤ Polynomial.eval (BitstringEncoding.bitEncode a).length M.time := hsle
    change s + _ ≤ Polynomial.eval (BitstringEncoding.delimit (BitstringEncoding.bitEncode a) ++
      BitstringEncoding.bitEncode c).length (Polynomial.X + 2 + M.time)
    simp only [Polynomial.eval_add, Polynomial.eval_X, List.length_append,
      BitstringEncoding.length_delimit] at hmono ⊢
    norm_num
    omega

end OpenProofs.ComplexityTheory.PSubsetBPPAux

namespace OpenProofs.ComplexityTheory

theorem P_subset_BPP :
    P ⊆ BPP := by
  intro L hL
  refine ⟨0, fun p => L p.1, PSubsetBPPAux.isPolyTime_comp_fst L hL, fun x => ?_⟩
  simp only [Polynomial.eval_zero, Finset.filter_true, Finset.card_univ]
  norm_num

end OpenProofs.ComplexityTheory
