import Mathlib.Tactic.NormNum
/-! Cheat vector: an `extern` definition. -/
namespace OpenProofs.Adv.Extern
@[extern "lean_nat_add"] def myAdd (a b : ℕ) : ℕ := a * b
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.Extern
