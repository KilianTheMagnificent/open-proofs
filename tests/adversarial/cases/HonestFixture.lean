import Mathlib.Tactic.NormNum
/-! Positive control: an honest proof of a fixture statement. -/
namespace OpenProofs.Adv.HonestFixture
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.HonestFixture
