import Mathlib.Data.Nat.Basic

/-! Adversarial-test fixture: a clean shared helper (copied to `OpenProofs/Lib/`). -/

namespace OpenProofs.Lib.AdvLibGood

theorem two_pow_ten_lib : (2 : ℕ) ^ 10 = 1024 := by decide

end OpenProofs.Lib.AdvLibGood
