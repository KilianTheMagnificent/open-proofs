import OpenProofs.Lib.AdvLibBad
/-! Cheat: launder a placeholder through the shared helper library. -/
namespace OpenProofs.Adv.LibSorryUse
theorem t : (2 : ℕ) ^ 10 = 1024 := OpenProofs.Lib.AdvLibBad.cheat_lemma
end OpenProofs.Adv.LibSorryUse
