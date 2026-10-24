import FormalConjectures.Millennium.PvsNP

/-!
# `ComplexityTheory.P_subset_NP`

Upstream: `ComplexityTheory.P_subset_NP` (category textbook), `FormalConjectures/Millennium/PvsNP.lean` line 83.
Proof idea: take the polynomial `0` and the verifier `R (x, w) = L x`. For a polynomial-time
TM2 machine `tm` deciding `L`, build an extended machine with two extra Boolean stacks (a new
input stack and a scratch stack). It first parses the self-delimiting block `delimit (enc x)` of
the pair encoding onto the scratch stack, drains the encoding of the witness, moves the scratch
stack (reversing it back) onto the input stack of `tm`, and then runs a lifted copy of `tm`
(`stepAux_lift`, `step_lift`: one step of the copy is one step of `tm`). Preprocessing takes
`2 |enc x| + |enc w| + 3` steps, so the total time is bounded by `n + 2 + time n`, using that
evaluation of a polynomial over `ℕ` is monotone.
-/

open ComplexityTheory Turing StateTransition

namespace OpenProofs.ComplexityTheory

namespace PSubNPAux

variable (tm : FinTM2)

/-- Stack alphabets of the extended machine: `inl false` is the new input stack, `inl true` a
scratch stack, `inr k` the stacks of `tm`. -/
abbrev Γ' : Bool ⊕ tm.K → Type
  | Sum.inl _ => Bool
  | Sum.inr k => tm.Γ k

/-- States of the extended machine. -/
abbrev σ' : Type := Option Bool × tm.σ

/-- Labels of the extended machine. -/
abbrev Λ' : Type := tm.Λ ⊕ Fin 3

/-- Lift a statement of `tm` to the extended machine. -/
noncomputable def liftStmt : TM2.Stmt tm.Γ tm.Λ tm.σ → TM2.Stmt (Γ' tm) (Λ' tm) (σ' tm)
  | .push k f q => .push (Sum.inr k) (fun s => f s.2) (liftStmt q)
  | .peek k f q => .peek (Sum.inr k) (fun s a => (s.1, f s.2 a)) (liftStmt q)
  | .pop k f q => .pop (Sum.inr k) (fun s a => (s.1, f s.2 a)) (liftStmt q)
  | .load f q => .load (fun s => (s.1, f s.2)) (liftStmt q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2) (liftStmt q₁) (liftStmt q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.2))
  | .halt => .halt

/-- Preprocessing: label `0` parses the self-delimiting block onto the scratch stack, label `1`
drains the rest of the input, label `2` moves the scratch stack onto the input stack of `tm`. -/
def pre (ia : Bool → tm.Γ tm.k₀) : Fin 3 → TM2.Stmt (Γ' tm) (Λ' tm) (σ' tm)
  | 0 => .pop (Sum.inl false) (fun s a => (a, s.2)) <|
      .branch (fun s => s.1 == some true)
        (.pop (Sum.inl false) (fun s a => (a, s.2)) <|
          .push (Sum.inl true) (fun s => s.1.getD false) <| .goto fun _ => Sum.inr 0)
        (.goto fun _ => Sum.inr 1)
  | 1 => .pop (Sum.inl false) (fun s a => (a, s.2)) <|
      .branch (fun s => s.1.isSome) (.goto fun _ => Sum.inr 1) (.goto fun _ => Sum.inr 2)
  | 2 => .pop (Sum.inl true) (fun s a => (a, s.2)) <|
      .branch (fun s => s.1.isSome)
        (.push (Sum.inr tm.k₀) (fun s => ia (s.1.getD false)) <| .goto fun _ => Sum.inr 2)
        (.goto fun _ => Sum.inl tm.main)

/-- The program of the extended machine. -/
noncomputable def mm (ia : Bool → tm.Γ tm.k₀) : Λ' tm → TM2.Stmt (Γ' tm) (Λ' tm) (σ' tm)
  | Sum.inl l => liftStmt tm (tm.m l)
  | Sum.inr i => pre tm ia i

/-- The extended machine. -/
noncomputable def machine (ia : Bool → tm.Γ tm.k₀) : FinTM2 :=
  haveI := tm.kFin; haveI := tm.ΛFin; haveI := tm.σFin
  { K := Bool ⊕ tm.K
    k₀ := Sum.inl false
    k₁ := Sum.inr tm.k₁
    Γ := Γ' tm
    Λ := Λ' tm
    main := Sum.inr 0
    σ := σ' tm
    initialState := (none, tm.initialState)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := mm tm ia }

/-- Stacks of the extended machine from an input stack, a scratch stack and stacks of `tm`. -/
def stk (inp aux : List Bool) (S : ∀ k, List (tm.Γ k)) : ∀ k : Bool ⊕ tm.K, List (Γ' tm k)
  | Sum.inl false => inp
  | Sum.inl true => aux
  | Sum.inr k => S k

theorem update_inp (inp aux : List Bool) (S : ∀ k, List (tm.Γ k)) (x : List Bool) :
    Function.update (stk tm inp aux S) (Sum.inl false) x = stk tm x aux S := by
  funext j
  rcases j with (_ | _) | j
  · exact Function.update_self _ _ _
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem update_aux (inp aux : List Bool) (S : ∀ k, List (tm.Γ k)) (x : List Bool) :
    Function.update (stk tm inp aux S) (Sum.inl true) x = stk tm inp x S := by
  funext j
  rcases j with (_ | _) | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · exact Function.update_self _ _ _
  · rw [Function.update_of_ne (by simp)]; rfl

theorem update_k (inp aux : List Bool) (S : ∀ k, List (tm.Γ k)) (k : tm.K) (x : List (tm.Γ k)) :
    Function.update (stk tm inp aux S) (Sum.inr k) x = stk tm inp aux (Function.update S k x) := by
  funext j
  rcases j with (_ | _) | j
  · rfl
  · rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      exact (Function.update_self (β := fun k => List (tm.Γ k)) j x S).symm
    · rw [Function.update_of_ne (by simpa using h)]
      exact (Function.update_of_ne (β := fun k => List (tm.Γ k)) h x S).symm

/-- Lift a configuration of `tm`. -/
def liftCfg (c : TM2.Cfg tm.Γ tm.Λ tm.σ) : TM2.Cfg (Γ' tm) (Λ' tm) (σ' tm) :=
  ⟨c.l.map Sum.inl, (none, c.var), stk tm [] [] c.stk⟩

theorem stepAux_lift (q : TM2.Stmt tm.Γ tm.Λ tm.σ) :
    ∀ (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      TM2.stepAux (liftStmt tm q) (none, v) (stk tm [] [] S) = liftCfg tm (TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    rw [show stk tm [] [] S (Sum.inr k) = S k from rfl, update_k, ih]
  | peek k f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    rw [show stk tm [] [] S (Sum.inr k) = S k from rfl, update_k, ih]
  | load f q ih =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [liftStmt, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => intro v S; rfl
  | halt => intro v S; rfl

theorem step_lift (ia : Bool → tm.Γ tm.k₀) (c : TM2.Cfg tm.Γ tm.Λ tm.σ) :
    TM2.step (mm tm ia) (liftCfg tm c) = (TM2.step tm.m c).map (liftCfg tm) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · simp only [liftCfg, Option.map_some, TM2.step, mm]
    rw [stepAux_lift]; rfl

theorem iterate_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] (none : Option α) = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem iterate_map {α β : Type} (f : α → Option α) (g : β → Option β) (φ : α → β)
    (hφ : ∀ a, g (φ a) = (f a).map φ) (n : ℕ) :
    ∀ o : Option α, (flip bind g)^[n] (o.map φ) = ((flip bind f)^[n] o).map φ := by
  induction n with
  | zero => intro o; rfl
  | succ n ih =>
    intro o
    rcases o with _ | a
    · show (flip bind g)^[n + 1] none = Option.map φ ((flip bind f)^[n + 1] none)
      rw [iterate_none, iterate_none]; rfl
    · simp only [Function.iterate_succ, Function.comp_apply, Option.map_some]
      have : flip bind g (some (φ a)) = (flip bind f (some a)).map φ := by
        simp [flip, hφ]
      rw [this, ih]

theorem evalsTo_map {α β : Type} {f : α → Option α} {g : β → Option β} (φ : α → β)
    (hφ : ∀ a, g (φ a) = (f a).map φ) {a : α} {b : Option α} {m : ℕ}
    (h : EvalsToInTime f a b m) : Nonempty (EvalsToInTime g (φ a) (b.map φ) m) :=
  ⟨⟨⟨h.steps, by
    have := iterate_map f g φ hφ h.steps (some a)
    rw [h.evals_in_steps] at this; exact this⟩, h.steps_le_m⟩⟩

theorem evalsTo_one {α : Type} {f : α → Option α} {a b : α} (h : f a = some b) :
    Nonempty (EvalsToInTime f a (some b) 1) :=
  ⟨⟨⟨1, by simp [flip, h]⟩, le_refl 1⟩⟩

theorem evalsTo_mono {α : Type} {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : Nonempty (EvalsToInTime f a b m)) (hm : m ≤ m') : Nonempty (EvalsToInTime f a b m') :=
  let ⟨h⟩ := h; ⟨⟨h.toEvalsTo, h.steps_le_m.trans hm⟩⟩

theorem evalsTo_trans {α : Type} {f : α → Option α} {a b : α} {c : Option α} {m₁ m₂ : ℕ}
    (h₁ : Nonempty (EvalsToInTime f a (some b) m₁)) (h₂ : Nonempty (EvalsToInTime f b c m₂)) :
    Nonempty (EvalsToInTime f a c (m₂ + m₁)) :=
  let ⟨h₁⟩ := h₁; let ⟨h₂⟩ := h₂; ⟨EvalsToInTime.trans f m₁ m₂ a b c h₁ h₂⟩

theorem initList_k₀ (t : List (tm.Γ tm.k₀)) : (initList tm t).stk tm.k₀ = t := by
  simp [initList]

theorem update_initList (t x : List (tm.Γ tm.k₀)) :
    Function.update (initList tm t).stk tm.k₀ x = (initList tm x).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; rw [Function.update_self]; simp [initList]
  · rw [Function.update_of_ne h]; simp [initList, h]

theorem phase1 (ia : Bool → tm.Γ tm.k₀) (S : ∀ k, List (tm.Γ k)) (w : tm.σ) (r : List Bool) :
    ∀ (e aux : List Bool) (v : Option Bool),
      Nonempty (EvalsToInTime (TM2.step (mm tm ia))
        ⟨some (Sum.inr 0), (v, w), stk tm (BitstringEncoding.delimit e ++ r) aux S⟩
        (some ⟨some (Sum.inr 1), (some false, w), stk tm r (e.reverse ++ aux) S⟩)
        (e.length + 1)) := by
  intro e
  induction e with
  | nil =>
    intro aux v
    apply evalsTo_one
    simp [TM2.step, mm, pre, BitstringEncoding.delimit, stk, update_inp]
  | cons b e ih =>
    intro aux v
    have h1 : TM2.step (mm tm ia)
        ⟨some (Sum.inr 0), (v, w), stk tm (BitstringEncoding.delimit (b :: e) ++ r) aux S⟩ =
        some ⟨some (Sum.inr 0), (some b, w), stk tm (BitstringEncoding.delimit e ++ r) (b :: aux) S⟩ := by
      simp [TM2.step, mm, pre, BitstringEncoding.delimit, stk, update_inp, update_aux]
    have h2 := evalsTo_trans (evalsTo_one h1) (ih (b :: aux) (some b))
    have h3 : (b :: e).reverse ++ aux = e.reverse ++ b :: aux := by simp
    rw [h3]
    exact evalsTo_mono h2 (by simp)

theorem phase2 (ia : Bool → tm.Γ tm.k₀) (S : ∀ k, List (tm.Γ k)) (w : tm.σ) (aux : List Bool) :
    ∀ (r : List Bool) (v : Option Bool),
      Nonempty (EvalsToInTime (TM2.step (mm tm ia))
        ⟨some (Sum.inr 1), (v, w), stk tm r aux S⟩
        (some ⟨some (Sum.inr 2), (none, w), stk tm [] aux S⟩) (r.length + 1)) := by
  intro r
  induction r with
  | nil =>
    intro v
    apply evalsTo_one
    simp [TM2.step, mm, pre, stk, update_inp]
  | cons b r ih =>
    intro v
    have h1 : TM2.step (mm tm ia) ⟨some (Sum.inr 1), (v, w), stk tm (b :: r) aux S⟩ =
        some ⟨some (Sum.inr 1), (some b, w), stk tm r aux S⟩ := by
      simp [TM2.step, mm, pre, stk, update_inp]
    exact evalsTo_mono (evalsTo_trans (evalsTo_one h1) (ih (some b))) (by simp)

theorem phase3 (ia : Bool → tm.Γ tm.k₀) (w : tm.σ) :
    ∀ (aux : List Bool) (t : List (tm.Γ tm.k₀)) (v : Option Bool),
      Nonempty (EvalsToInTime (TM2.step (mm tm ia))
        ⟨some (Sum.inr 2), (v, w), stk tm [] aux (initList tm t).stk⟩
        (some ⟨some (Sum.inl tm.main), (none, w),
          stk tm [] [] (initList tm (aux.reverse.map ia ++ t)).stk⟩) (aux.length + 1)) := by
  intro aux
  induction aux with
  | nil =>
    intro t v
    apply evalsTo_one
    simp [TM2.step, mm, pre, stk, update_aux]
  | cons b aux ih =>
    intro t v
    have h1 : TM2.step (mm tm ia) ⟨some (Sum.inr 2), (v, w), stk tm [] (b :: aux) (initList tm t).stk⟩ =
        some ⟨some (Sum.inr 2), (some b, w), stk tm [] aux (initList tm (ia b :: t)).stk⟩ := by
      simp [TM2.step, mm, pre, stk, update_aux, update_k, initList_k₀, update_initList]
    have h2 := evalsTo_trans (evalsTo_one h1) (ih (ia b :: t) (some b))
    have h3 : (b :: aux).reverse.map ia ++ t = aux.reverse.map ia ++ ia b :: t := by simp
    rw [h3]
    exact evalsTo_mono h2 (by simp)

theorem initList_machine (ia : Bool → tm.Γ tm.k₀) (l : List Bool) :
    initList (machine tm ia) l =
      (⟨some (Sum.inr 0), (none, tm.initialState), stk tm l [] (initList tm []).stk⟩ :
        TM2.Cfg (Γ' tm) (Λ' tm) (σ' tm)) := by
  unfold initList
  congr 1
  funext k
  rcases k with (_ | _) | k
  · rfl
  · rfl
  · show _ = (initList tm []).stk k
    by_cases h : k = tm.k₀
    · subst h; simp [initList]; rfl
    · simp [initList, h]; rfl

theorem haltList_machine (ia : Bool → tm.Γ tm.k₀) (s : List (tm.Γ tm.k₁)) :
    haltList (machine tm ia) s = liftCfg tm (haltList tm s) := by
  unfold haltList liftCfg
  congr 1
  funext k
  rcases k with (_ | _) | k
  · rfl
  · rfl
  · show _ = (haltList tm s).stk k
    by_cases h : k = tm.k₁
    · subst h
      split
      · simp [haltList]; rfl
      · exact absurd rfl ‹_›
    · split
      · exact absurd (Sum.inr.inj ‹_›) h
      · simp [haltList, h]; rfl

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

theorem outputs (ia : Bool → tm.Γ tm.k₀) (e r : List Bool) (out : List (tm.Γ tm.k₁)) (T : ℕ)
    (hM : TM2OutputsInTime tm (List.map ia e) (some out) T) (l : List Bool)
    (hl : l = BitstringEncoding.delimit e ++ r) :
    Nonempty (EvalsToInTime (machine tm ia).step (initList (machine tm ia) l)
      (some (haltList (machine tm ia) out)) (T + (e.length + 1) + (r.length + 1) + (e.length + 1))) := by
  subst hl
  have h1 := phase1 tm ia (initList tm []).stk tm.initialState r e [] none
  have h2 := phase2 tm ia (initList tm []).stk tm.initialState (e.reverse ++ []) r (some false)
  have h3 := phase3 tm ia tm.initialState (e.reverse ++ []) [] none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h1 h2 h3
  have h4 := evalsTo_map (liftCfg tm) (step_lift tm ia) hM
  simp only [Option.map_some] at h4
  rw [initList_machine, haltList_machine]
  exact evalsTo_trans h1 (evalsTo_trans h2 (evalsTo_trans h3 h4))

end PSubNPAux

theorem P_subset_NP :
    P ⊆ NP := by
  intro L hL
  obtain ⟨M⟩ := hL
  refine ⟨0, fun xw => L xw.1, ?_, fun x => ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩⟩
  refine ⟨{ tm := PSubNPAux.machine M.tm M.inputAlphabet.invFun
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := M.outputAlphabet
            time := Polynomial.X + 2 + M.time
            outputsFun := fun xw => Classical.choice ?_ }⟩
  obtain ⟨x, w⟩ := xw
  refine PSubNPAux.evalsTo_mono (PSubNPAux.outputs M.tm M.inputAlphabet.invFun
    (BitstringEncoding.instList.encode x) (BitstringEncoding.instList.encode w) _ _
    (M.outputsFun x) _ ?_) ?_
  · exact List.map_id _
  · show _ ≤ Polynomial.eval (BitstringEncoding.delimit (BitstringEncoding.instList.encode x) ++
      BitstringEncoding.instList.encode w).length (Polynomial.X + 2 + M.time)
    have := PSubNPAux.eval_mono M.time (show (BitstringEncoding.instList.encode x).length ≤
      2 * (BitstringEncoding.instList.encode x).length + 1 +
        (BitstringEncoding.instList.encode w).length by omega)
    simp only [List.length_append, BitstringEncoding.length_delimit, Polynomial.eval_add,
      Polynomial.eval_X]
    simp
    omega

end OpenProofs.ComplexityTheory
