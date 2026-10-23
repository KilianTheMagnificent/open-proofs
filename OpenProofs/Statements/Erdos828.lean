import FormalConjectures.ErdosProblems.«828»

/-!
# Self-recorded special cases of Erdős 828

Upstream `Erdos828.erdos_828 : ∀ a : ℤ, Set.Infinite {n : ℕ | ↑(φ n) ∣ n + a}` is open.
Each statement below is that statement at a fixed `a`, written as `type_of% (Erdos828.erdos_828 a)`
so the specialization is mechanical (the elaborated type is the upstream body with `a`
substituted; the upstream theorem itself does not occur in it).
-/

namespace OpenProofs.Statements.Erdos828

/-- Erdős 828 at `a = 0`: infinitely many `n` with `φ n ∣ n`. -/
theorem at_zero : type_of% (Erdos828.erdos_828 0) := by sorry

/-- Erdős 828 at `a = -1`: infinitely many `n` with `φ n ∣ n - 1`. -/
theorem at_neg_one : type_of% (Erdos828.erdos_828 (-1)) := by sorry

end OpenProofs.Statements.Erdos828
