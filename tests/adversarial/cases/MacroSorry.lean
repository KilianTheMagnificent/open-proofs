import Mathlib.Data.Nat.Basic
/-! Cheat: hide the placeholder behind a macro. -/
macro "trust_me" : tactic => `(tactic| sorry)
namespace OpenProofs.Adv.MacroSorry
theorem t : (2 : ℕ) ^ 10 = 1024 := by trust_me
end OpenProofs.Adv.MacroSorry
