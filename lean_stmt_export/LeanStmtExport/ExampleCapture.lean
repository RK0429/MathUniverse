import Lean
import Lean.Elab
import Lean.Elab.Command
import Lean.Elab.Term

namespace LeanStmtExport.ExampleCapture

open Lean Elab Command Term

-- IO ref to accumulate example dependencies
initialize exampleMapRef : IO.Ref (NameMap (Array Name)) ← IO.mkRef {}

/-- Record dependencies for a synthetic example -/
def recordExample (exName : Name) (deps : Array Name) : CommandElabM Unit :=
  exampleMapRef.modify fun m => m.insert exName deps

/-- Read the accumulated example dependency map -/
def readExampleMap : IO (NameMap (Array Name)) :=
  exampleMapRef.get

/-- Custom `example` command syntax and elaborator to capture examples -/
syntax (name := exampleCommand) "example" term : command

@[command_elab exampleCommand] def elabExample : CommandElab :=
  fun stx => do
    let termExpr ← liftTermElabM (Term.elabTerm stx[1] none)
    let deps      := termExpr.getUsedConstantsAsSet.toArray
    let exName    ← liftCoreM (mkFreshUserName `example)
    recordExample exName deps

end LeanStmtExport.ExampleCapture
