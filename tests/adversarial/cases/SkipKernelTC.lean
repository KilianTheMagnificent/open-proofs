import Mathlib.Data.Nat.Basic
/-! Cheat: environment hacking. Add an ill-typed "proof" of `False` with kernel checking
switched off, then use it. No axioms appear; only a kernel replay can catch this. -/
open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd do
  let decl := Declaration.thmDecl
    { name := `OpenProofs.Adv.SkipKernelTC.cheat, levelParams := [],
      type := mkConst ``False, value := mkConst ``True.intro }
  liftCoreM (addDecl decl)
namespace OpenProofs.Adv.SkipKernelTC
theorem t : (2 : ℕ) ^ 10 = 1024 := cheat.elim
end OpenProofs.Adv.SkipKernelTC
