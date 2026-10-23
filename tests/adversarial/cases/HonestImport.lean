import FormalConjectures.ErdosProblems.«349»
/-! Honest module used to test claims that point at the wrong declaration. -/
namespace OpenProofs.Adv.HonestImport
theorem t : (2 : ℕ) ^ 10 = 1024 := by norm_num
end OpenProofs.Adv.HonestImport
