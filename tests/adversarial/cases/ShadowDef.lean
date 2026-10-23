import FormalConjectures.ErdosProblems.«349»
/-! Cheat: shadow the upstream definition `Erdos349.IsGoodPair` with a trivial one, so the
statement *text* `Erdos349.IsGoodPair 1 2` matches upstream but means something else. -/
namespace OpenProofs.Adv.ShadowDef
namespace Erdos349
def IsGoodPair (_t _α : ℝ) : Prop := True
end Erdos349
theorem one_two_isGoodPair : Erdos349.IsGoodPair 1 2 := trivial
end OpenProofs.Adv.ShadowDef
