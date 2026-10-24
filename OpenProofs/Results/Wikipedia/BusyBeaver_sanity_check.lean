import FormalConjectures.Wikipedia.BusyBeaver

/-!
# `BusyBeaver.sanity_check`

Upstream: `BusyBeaver.sanity_check` (category API), `FormalConjectures/Wikipedia/BusyBeaver.lean` line 67.
Proof idea: the two sets inside `sSup` are equal. A machine on `Fin 2`/`Fin n` is itself a
candidate. Conversely, a candidate's symbol and state types have cardinality 2 and `n`, so there
are equivalences to `Fin 2` and `Fin n` sending the default element to the default element
(compose any equivalence with a swap). Transporting the machine along them commutes with
`step` (tapes are mapped by the pointed map `Tape.map`), hence with `multiStep`, and the
initial configuration goes to the initial configuration; so `HaltsAfter`, `IsHalting` and the
halting number are preserved.
-/

open Turing BusyBeaver
open BusyBeaver

namespace OpenProofs.BusyBeaver

section Transport

variable {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']

/-- Transport a busy beaver machine along equivalences of symbols and states. -/
noncomputable def bbTransportMachine (e : Γ ≃ Γ') (f : Λ ≃ Λ')
    (M : Turing.BusyBeaver.Machine Γ Λ) : Turing.BusyBeaver.Machine Γ' Λ' :=
  fun q a => (M (f.symm q) (e.symm a)).map
    fun p => (p.1.map f, ⟨e p.2.symbol, p.2.dir⟩)

/-- Transport a configuration along equivalences of symbols and states. -/
def bbTransportCfg (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (c : Turing.BusyBeaver.Cfg Γ Λ) : Turing.BusyBeaver.Cfg Γ' Λ' :=
  ⟨c.q.map f, c.tape.map ⟨e, he⟩⟩

theorem bbTransport_step (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (M : Turing.BusyBeaver.Machine Γ Λ) (c : Turing.BusyBeaver.Cfg Γ Λ) :
    (bbTransportMachine e f M).step (bbTransportCfg e he f c) =
      (M.step c).map (bbTransportCfg e he f) := by
  rcases c with ⟨_ | q, T⟩
  · rfl
  · simp only [bbTransportCfg, Option.map_some, Turing.BusyBeaver.Machine.step,
      bbTransportMachine, Tape.map_fst, Equiv.symm_apply_apply]
    rcases h : M q T.1 with _ | ⟨q', ⟨a, d⟩⟩
    · rfl
    · simp only [bbTransportCfg, Option.map_some, Tape.map_move, Tape.map_write]

theorem bbTransport_multiStep (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (M : Turing.BusyBeaver.Machine Γ Λ) (c : Turing.BusyBeaver.Cfg Γ Λ) (k : ℕ) :
    (bbTransportMachine e f M).multiStep (bbTransportCfg e he f c) k =
      (M.multiStep c k).map (bbTransportCfg e he f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Turing.BusyBeaver.Machine.multiStep_succ, Turing.BusyBeaver.Machine.multiStep_succ, ih]
    rcases M.multiStep c k with _ | c'
    · rfl
    · simp [bbTransport_step]

theorem bbTransport_init (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (hf : f default = default) :
    bbTransportCfg e he f (Turing.BusyBeaver.Machine.init [] : Turing.BusyBeaver.Cfg Γ Λ) =
      Turing.BusyBeaver.Machine.init [] := by
  simp [bbTransportCfg, Turing.BusyBeaver.Machine.init, hf, Tape.map_mk₁]

theorem bbTransport_haltsAfter_iff (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (hf : f default = default) (M : Turing.BusyBeaver.Machine Γ Λ) (k : ℕ) :
    (bbTransportMachine e f M).HaltsAfter (Turing.BusyBeaver.Machine.init []) k ↔
      M.HaltsAfter (Turing.BusyBeaver.Machine.init []) k := by
  rw [Turing.BusyBeaver.Machine.HaltsAfter, Turing.BusyBeaver.Machine.HaltsAfter,
    ← bbTransport_init e he f hf, bbTransport_multiStep]
  simp

theorem bbTransport_haltingNumber (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (hf : f default = default) (M : Turing.BusyBeaver.Machine Γ Λ) :
    (bbTransportMachine e f M).haltingNumber = M.haltingNumber := by
  unfold Turing.BusyBeaver.Machine.haltingNumber
  simp only [bbTransport_haltsAfter_iff e he f hf]

theorem bbTransport_isHalting (e : Γ ≃ Γ') (he : e default = default) (f : Λ ≃ Λ')
    (hf : f default = default) (M : Turing.BusyBeaver.Machine Γ Λ) [M.IsHalting] :
    (bbTransportMachine e f M).IsHalting := by
  have h := (Turing.BusyBeaver.Machine.isHalting_iff_exists_haltsAt M).mp inferInstance
  rw [Turing.BusyBeaver.Machine.isHalting_iff_exists_haltsAt]
  simpa only [bbTransport_haltsAfter_iff e he f hf] using h

end Transport

theorem bbExists_pointed_equiv {α β : Type*} [Fintype α] [Fintype β] [Inhabited α]
    [Inhabited β] [DecidableEq β] (h : Fintype.card α = Fintype.card β) :
    ∃ e : α ≃ β, e default = default := by
  let e0 := Fintype.equivOfCardEq h
  exact ⟨e0.trans (Equiv.swap (e0 default) default), by simp [Equiv.swap_apply_left]⟩

theorem bbHaltingNumber_ne_top {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.BusyBeaver.Machine Γ Λ) [M.IsHalting] : M.haltingNumber ≠ ⊤ := by
  obtain ⟨k, hk⟩ := (Turing.BusyBeaver.Machine.isHalting_iff_exists_haltsAt M).mp inferInstance
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top k) (sInf_le ?_)
  exact ⟨k, hk, rfl⟩

instance bbFiniteMachine (n : ℕ) [NeZero n] :
    Finite (Turing.BusyBeaver.Machine (Fin 2) (Fin n)) := by
  have : Finite Dir :=
    Finite.of_injective (fun d : Dir => match d with | .left => true | .right => false)
      (by intro a b; cases a <;> cases b <;> simp)
  have : Finite (Turing.BusyBeaver.Stmt (Fin 2)) :=
    Finite.of_injective (fun s : Turing.BusyBeaver.Stmt (Fin 2) => (s.symbol, s.dir))
      (by rintro ⟨a, b⟩ ⟨c, d⟩ h; simp_all)
  unfold Turing.BusyBeaver.Machine
  infer_instance

theorem sanity_check (n : ℕ) [NeZero n] :
    BB n = sSup {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting),
      M.haltingNumber = N} := by
  set T : Set ℕ∞ := {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting),
      M.haltingNumber = N} with hT
  -- the set defining `BB n` is the preimage of `T`
  have hS : {N : ℕ | ∃ C : Candidate n, C.M.haltingNumber = N} = (fun k : ℕ => (k : ℕ∞)) ⁻¹' T := by
    ext N
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hT]
    constructor
    · rintro ⟨C, hC⟩
      obtain ⟨e, he⟩ := bbExists_pointed_equiv (α := C.Γ) (β := Fin 2)
        (C.Γ_card.trans (Fintype.card_fin 2).symm)
      obtain ⟨f, hf⟩ := bbExists_pointed_equiv (α := C.Λ) (β := Fin n)
        (C.Λ_card.trans (Fintype.card_fin n).symm)
      have := C.M_isHalting
      exact ⟨bbTransportMachine e f C.M, bbTransport_isHalting e he f hf C.M,
        (bbTransport_haltingNumber e he f hf C.M).trans hC⟩
    · rintro ⟨M, hM, hMN⟩
      exact ⟨⟨Fin 2, Fin n, inferInstance, Fintype.card_fin 2, inferInstance, inferInstance,
        Fintype.card_fin n, inferInstance, M, hM⟩, hMN⟩
  have hTfin : T.Finite := by
    have : T ⊆ Set.range (fun M : Machine (Fin 2) (Fin n) => M.haltingNumber) := by
      rintro _ ⟨M, _, rfl⟩
      exact ⟨M, rfl⟩
    exact (Set.finite_range _).subset this
  have hTsub : T ⊆ Set.range (fun k : ℕ => (k : ℕ∞)) := by
    rintro _ ⟨M, hM, rfl⟩
    exact ENat.ne_top_iff_exists.mp (bbHaltingNumber_ne_top M)
  have hSfin : ((fun k : ℕ => (k : ℕ∞)) ⁻¹' T).Finite :=
    hTfin.preimage (Nat.cast_injective.injOn)
  unfold BB
  rw [hS, ENat.natCast_sSup hSfin.bddAbove, ← sSup_image, Set.image_preimage_eq_of_subset hTsub]

end OpenProofs.BusyBeaver
