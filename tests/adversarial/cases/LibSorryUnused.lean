import OpenProofs.Lib.AdvLibBad
/-! Hygiene: importing a helper module that contains a placeholder is rejected even if the
placeholder lemma is not used. -/
namespace OpenProofs.Adv.LibSorryUnused
theorem t : (2 : ℕ) ^ 10 = 1024 := by decide
end OpenProofs.Adv.LibSorryUnused
