import Mathlib.Tactic.NormNum
/-! Cheat vector: an `opaque` constant. -/
namespace OpenProofs.Adv.OpaqueDecl
opaque secret : ℕ
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.OpaqueDecl
