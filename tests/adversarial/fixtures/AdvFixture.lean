import Mathlib.Data.Nat.Basic

/-! Adversarial-test fixture: self-recorded variant statements.
Copied to `OpenProofs/Statements/AdvFixture.lean` by `tests/run_adversarial.py`. -/

namespace OpenProofs.Statements.AdvFixture

theorem two_pow_ten : (2 : ℕ) ^ 10 = 1024 := by sorry

theorem le_succ_all : ∀ n : ℕ, n ≤ n + 1 := by sorry

end OpenProofs.Statements.AdvFixture
