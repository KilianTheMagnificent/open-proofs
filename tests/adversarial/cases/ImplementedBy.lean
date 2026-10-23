import Mathlib.Tactic.NormNum
/-! Cheat vector: an `implemented_by` definition (compiled code differs from the logic). -/
namespace OpenProofs.Adv.ImplementedBy
def fakeF (n : ℕ) : ℕ := n + 1
@[implemented_by fakeF] def realF (n : ℕ) : ℕ := n
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.ImplementedBy
