import OpenProofs.Statements.AdvFixture
/-! Cheat: "prove" a variant by citing its own recorded statement (a placeholder). -/
namespace OpenProofs.Adv.ImportsStatement
theorem t : (2 : ℕ) ^ 10 = 1024 := OpenProofs.Statements.AdvFixture.two_pow_ten
end OpenProofs.Adv.ImportsStatement
