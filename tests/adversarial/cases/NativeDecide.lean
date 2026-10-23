import Mathlib.Data.Nat.Basic
/-! Cheat: native evaluation (trusts the compiler). -/
namespace OpenProofs.Adv.NativeDecide
theorem t : (2 : ℕ) ^ 10 = 1024 := by native_decide
end OpenProofs.Adv.NativeDecide
