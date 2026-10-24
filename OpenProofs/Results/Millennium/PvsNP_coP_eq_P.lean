import FormalConjectures.Millennium.PvsNP

/-!
# `ComplexityTheory.coP_eq_P`

Upstream: `ComplexityTheory.coP_eq_P` (category textbook), `FormalConjectures/Millennium/PvsNP.lean` line 70.
Proof idea: given a polynomial-time TM2 machine deciding `L`, build a machine with the same
stacks, labels and program, whose state carries one extra bit, and in which every `halt`
statement is replaced by "pop the output stack into the extra bit, push the encoding of its
negation, reset the bit, halt". Since a whole statement is executed in one step, the new machine
takes exactly as many steps as the old one, and its run is the image of the old run under a
configuration map that negates the top of the output stack on halted configurations. So
`Lᶜ = not ∘ L` is decided within the same polynomial bound. Applying this twice gives equality.
-/

open ComplexityTheory

namespace OpenProofs.ComplexityTheory

namespace CoPNeg

open Turing StateTransition

noncomputable section

variable (tm : FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)

/-- The symbol pushed in place of the popped output symbol `o`: the encoding of its negation. -/
def negSym (o : Option (tm.Γ tm.k₁)) : tm.Γ tm.k₁ := e.symm (!(o.elim false e))

/-- The program translation: the extra state bit is carried along, and `halt` negates the top
of the output stack before halting. -/
def trStmt (q : TM2.Stmt tm.Γ tm.Λ tm.σ) : TM2.Stmt tm.Γ tm.Λ (tm.σ × Bool) :=
  TM2.Stmt.rec (motive := fun _ => TM2.Stmt tm.Γ tm.Λ (tm.σ × Bool))
    (fun k f _ q' => .push k (fun v => f v.1) q')
    (fun k f _ q' => .peek k (fun v o => (f v.1 o, v.2)) q')
    (fun k f _ q' => .pop k (fun v o => (f v.1 o, v.2)) q')
    (fun a _ q' => .load (fun v => (a v.1, v.2)) q')
    (fun f _ _ q₁ q₂ => .branch (fun v => f v.1) q₁ q₂)
    (fun f => .goto (fun v => f v.1))
    (.pop tm.k₁ (fun v o => (v.1, o.elim false e))
      (.push tm.k₁ (fun v => e.symm (!v.2)) (.load (fun v => (v.1, false)) .halt)))
    q

section trStmtEqns

variable {tm e}

theorem trStmt_push (k) (f : tm.σ → tm.Γ k) (q) :
    trStmt tm e (.push k f q) = .push k (fun v => f v.1) (trStmt tm e q) := rfl

theorem trStmt_peek (k) (f : tm.σ → Option (tm.Γ k) → tm.σ) (q) :
    trStmt tm e (.peek k f q) = .peek k (fun v o => (f v.1 o, v.2)) (trStmt tm e q) := rfl

theorem trStmt_pop (k) (f : tm.σ → Option (tm.Γ k) → tm.σ) (q) :
    trStmt tm e (.pop k f q) = .pop k (fun v o => (f v.1 o, v.2)) (trStmt tm e q) := rfl

theorem trStmt_load (a : tm.σ → tm.σ) (q) :
    trStmt tm e (.load a q) = .load (fun v => (a v.1, v.2)) (trStmt tm e q) := rfl

theorem trStmt_branch (f : tm.σ → Bool) (q₁ q₂) :
    trStmt tm e (.branch f q₁ q₂) = .branch (fun v => f v.1) (trStmt tm e q₁) (trStmt tm e q₂) :=
  rfl

theorem trStmt_halt :
    trStmt tm e .halt = .pop tm.k₁ (fun v o => (v.1, o.elim false e))
      (.push tm.k₁ (fun v => e.symm (!v.2)) (.load (fun v => (v.1, false)) .halt)) := rfl

end trStmtEqns

/-- The negating machine. -/
def negTM : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := tm.Γ
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ × Bool
  initialState := (tm.initialState, false)
  σFin := @instFintypeProd _ _ tm.σFin _
  Γk₀Fin := tm.Γk₀Fin
  m l := trStmt tm e (tm.m l)

/-- Negate the top of the output stack. -/
def negStk (S : ∀ k, List (tm.Γ k)) : ∀ k, List (tm.Γ k) :=
  Function.update S tm.k₁ (negSym tm e (S tm.k₁).head? :: (S tm.k₁).tail)

/-- Configurations of `tm` mapped to configurations of `negTM tm e`. -/
def liftCfg : TM2.Cfg tm.Γ tm.Λ tm.σ → TM2.Cfg tm.Γ tm.Λ (tm.σ × Bool)
  | ⟨some l, v, S⟩ => ⟨some l, (v, false), S⟩
  | ⟨none, v, S⟩ => ⟨none, (v, false), negStk tm e S⟩

theorem stepAux_trStmt (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    TM2.stepAux (trStmt tm e q) (v, false) S = liftCfg tm e (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp [trStmt_push, ih]
  | peek k f q ih => simp [trStmt_peek, ih]
  | pop k f q ih => simp [trStmt_pop, ih]
  | load a q ih => simp [trStmt_load, ih]
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trStmt_branch, TM2.stepAux]
    cases f v <;> simp [ih₁, ih₂]
  | goto f => rfl
  | halt => simp [trStmt_halt, liftCfg, negStk, negSym]

theorem step_liftCfg (c : tm.Cfg) :
    (negTM tm e).step (liftCfg tm e c) = (tm.step c).map (liftCfg tm e) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · exact congrArg some (stepAux_trStmt tm e (tm.m l) v S)

theorem iterate_liftCfg (n : ℕ) (x : Option tm.Cfg) :
    (flip bind (negTM tm e).step)^[n] (x.map (liftCfg tm e)) =
      ((flip bind tm.step)^[n] x).map (liftCfg tm e) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    rcases x with _ | c
    · rfl
    · exact step_liftCfg tm e c

theorem liftCfg_initList (s : List (tm.Γ tm.k₀)) :
    liftCfg tm e (initList tm s) = initList (negTM tm e) s := rfl

theorem negStk_haltList (b : Bool) :
    negStk tm e (haltList tm [e.symm b]).stk = (haltList tm [e.symm (!b)]).stk := by
  funext k
  by_cases h : k = tm.k₁
  · subst h
    simp [haltList, negStk, negSym]
  · simp [haltList, negStk, h]

theorem liftCfg_haltList (b : Bool) :
    liftCfg tm e (haltList tm [e.symm b]) = haltList (negTM tm e) [e.symm (!b)] :=
  congrArg (fun S => (⟨none, (tm.initialState, false), S⟩ : TM2.Cfg tm.Γ tm.Λ (tm.σ × Bool)))
    (negStk_haltList tm e b)

end

end CoPNeg

open Turing StateTransition in
theorem compl_mem_P_of_mem_P {L : DecisionProblem} (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨M⟩ := h
  refine ⟨{ tm := CoPNeg.negTM M.tm M.outputAlphabet
            inputAlphabet := M.inputAlphabet
            outputAlphabet := M.outputAlphabet
            time := M.time
            outputsFun := fun a => ?_ }⟩
  have H := M.outputsFun a
  refine ⟨⟨H.steps, ?_⟩, H.steps_le_m⟩
  have h1 := congrArg (Option.map (CoPNeg.liftCfg M.tm M.outputAlphabet)) H.evals_in_steps
  rw [← CoPNeg.iterate_liftCfg] at h1
  exact h1.trans (congrArg some (CoPNeg.liftCfg_haltList M.tm M.outputAlphabet (L a)))


theorem coP_eq_P :
    { L | Lᶜ ∈ P } = P := by
  ext L
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    simpa using compl_mem_P_of_mem_P h
  · exact compl_mem_P_of_mem_P

end OpenProofs.ComplexityTheory
