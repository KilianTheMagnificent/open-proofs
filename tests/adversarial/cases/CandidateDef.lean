import Mathlib.Data.Nat.Basic
/-! A candidate definition that a bad statement fixture depends on. -/
namespace OpenProofs.Adv.CandidateDef
def Trivial : Prop := True
theorem t : Trivial := True.intro
end OpenProofs.Adv.CandidateDef
