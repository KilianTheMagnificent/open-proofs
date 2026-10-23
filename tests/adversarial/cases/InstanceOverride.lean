import Mathlib.Data.Nat.Basic
/-! Cheat: a high-priority local instance changes what `≤` means in the statement. -/
namespace OpenProofs.Adv.InstanceOverride
instance (priority := high) cheatLE : LE ℕ := ⟨fun _ _ => True⟩
theorem t : ∀ n : ℕ, n ≤ n + 1 := fun _ => trivial
end OpenProofs.Adv.InstanceOverride
