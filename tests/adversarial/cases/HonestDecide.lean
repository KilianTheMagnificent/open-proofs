import Mathlib.Data.Nat.Basic
/-! Positive control: kernel `decide` is allowed (no extra axioms). -/
namespace OpenProofs.Adv.HonestDecide
theorem t : (2 : ℕ) ^ 10 = 1024 := by decide
end OpenProofs.Adv.HonestDecide
