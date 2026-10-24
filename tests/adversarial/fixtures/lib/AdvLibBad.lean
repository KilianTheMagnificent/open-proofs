import Mathlib.Data.Nat.Basic

/-! Adversarial-test fixture: a shared helper hiding a placeholder (copied to `OpenProofs/Lib/`). -/

namespace OpenProofs.Lib.AdvLibBad

theorem cheat_lemma : (2 : ℕ) ^ 10 = 1024 := by sorry

theorem honest_lemma : (1 : ℕ) + 1 = 2 := rfl

end OpenProofs.Lib.AdvLibBad
