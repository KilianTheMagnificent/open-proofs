import Mathlib.Tactic.NormNum
/-! Cheat vector: `partial` and `unsafe` definitions. -/
namespace OpenProofs.Adv.UnsafePartial
partial def loop (n : ℕ) : ℕ := loop (n + 1)
unsafe def u : ℕ := 0
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.UnsafePartial
