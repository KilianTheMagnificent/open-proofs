import OpenProofs.Lib.AdvLibGood
/-! Positive control: a result that uses a clean shared helper from `OpenProofs/Lib`. -/
namespace OpenProofs.Adv.LibGoodUse
theorem t : (2 : ℕ) ^ 10 = 1024 := OpenProofs.Lib.AdvLibGood.two_pow_ten_lib
end OpenProofs.Adv.LibGoodUse
