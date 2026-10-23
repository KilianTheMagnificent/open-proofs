import Mathlib.Tactic.NormNum
/-! Hygiene violation: a declaration outside the `OpenProofs` namespace. -/
theorem helper_root : True := trivial
namespace OpenProofs.Adv.OutsideNamespace
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.OutsideNamespace
