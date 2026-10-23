import Mathlib.Data.Nat.Basic
/-! A proof that does not compile. -/
namespace OpenProofs.Adv.BrokenProof
theorem t : (2 : ℕ) ^ 10 = 1024 := rfl.symm.trans (Nat.succ_ne_zero 3)
end OpenProofs.Adv.BrokenProof
