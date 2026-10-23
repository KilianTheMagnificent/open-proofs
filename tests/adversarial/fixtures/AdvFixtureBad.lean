import OpenProofs.Adversarial.CandidateDef

/-! Adversarial-test fixture: a "statement" that depends on a candidate definition. -/

namespace OpenProofs.Statements.AdvFixtureBad

theorem trivial_holds : OpenProofs.Adv.CandidateDef.Trivial := by sorry

end OpenProofs.Statements.AdvFixtureBad
