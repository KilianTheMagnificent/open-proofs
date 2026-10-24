import FormalConjectures.Wikipedia.BusyBeaver

/-!
# `BusyBeaver.BB_1`

Upstream: `BusyBeaver.BB_1` (category test), `FormalConjectures/Wikipedia/BusyBeaver.lean` line 74.
Proof idea: a candidate has one state, so its first transition (state `default`, blank head)
either stops at once (0 steps), moves to the halting state (1 step), or re-enters the only state.
In the last case the head always lands on a fresh blank cell (`bb1_multiStep_left`/`_right`), so
the same transition repeats forever, contradicting `M_isHalting`. Hence every halting number is
at most 1, and `Bool`/`Unit` with the transition "write blank, move right, halt" attains 1.
-/

open Turing BusyBeaver
open BusyBeaver

namespace OpenProofs.BusyBeaver

section

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- A one-state loop that writes `a` and moves left keeps the head on a blank cell with a blank
left half-tape, so it never stops. -/
lemma bb1_multiStep_left (M : Machine Γ Λ) (a : Γ)
    (h : M default default = some (some default, ⟨a, Dir.left⟩)) (n : ℕ) :
    ∃ R, M.multiStep (Machine.init []) n = some ⟨some default, ⟨default, default, R⟩⟩ := by
  induction n with
  | zero => exact ⟨default, rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R.cons a, ?_⟩
    rw [Machine.multiStep_succ, hR, Option.bind_some]
    show (M default default).map _ = _
    rw [h]
    rfl

lemma bb1_multiStep_right (M : Machine Γ Λ) (a : Γ)
    (h : M default default = some (some default, ⟨a, Dir.right⟩)) (n : ℕ) :
    ∃ L, M.multiStep (Machine.init []) n = some ⟨some default, ⟨default, L, default⟩⟩ := by
  induction n with
  | zero => exact ⟨default, rfl⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih
    refine ⟨L.cons a, ?_⟩
    rw [Machine.multiStep_succ, hL, Option.bind_some]
    show (M default default).map _ = _
    rw [h]
    rfl

lemma bb1_haltsAfter_one [Subsingleton Λ] (M : Machine Γ Λ) [hM : M.IsHalting] :
    M.HaltsAfter (Machine.init []) 1 := by
  have h0 : (Machine.init [] : Cfg Γ Λ) = ⟨some default, ⟨default, default, default⟩⟩ := rfl
  rw [Machine.HaltsAfter, Machine.multiStep_succ, Machine.multiStep_one, h0]
  rcases hq : M default default with _ | ⟨_ | q, ⟨a, d⟩⟩
  · show ((M default default).map _).bind M.step = none
    rw [hq]
    rfl
  · show ((M default default).map _).bind M.step = none
    rw [hq]
    rfl
  · exfalso
    obtain rfl : q = default := Subsingleton.elim _ _
    obtain ⟨n, hn⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hM
    rw [Machine.HaltsAfter] at hn
    cases d with
    | left =>
      obtain ⟨R, hR⟩ := bb1_multiStep_left M a hq (n + 1)
      rw [hR] at hn
      exact Option.some_ne_none _ hn
    | right =>
      obtain ⟨L, hL⟩ := bb1_multiStep_right M a hq (n + 1)
      rw [hL] at hn
      exact Option.some_ne_none _ hn

end

theorem BB_1 : BB 1 = 1 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨⟨Bool, Unit, inferInstance, rfl, inferInstance, inferInstance, rfl, inferInstance,
    fun _ _ => some (none, ⟨default, Dir.right⟩),
    (Machine.isHalting_iff_exists_haltsAt _).mpr ⟨1, rfl⟩⟩, ?_⟩, ?_⟩
  · exact Machine.haltingNumber_def _ 1 ⟨_, rfl⟩ rfl
  · rintro N ⟨C, hC⟩
    have : Subsingleton C.Λ := Fintype.card_le_one_iff_subsingleton.mp C.Λ_card.le
    have := C.M_isHalting
    have h1 : C.M.haltingNumber ≤ ((1 : ℕ) : ENat) := sInf_le ⟨1, bb1_haltsAfter_one C.M, rfl⟩
    rw [hC] at h1
    exact_mod_cast h1

end OpenProofs.BusyBeaver
