import Lean
open Lean

namespace GenDecls.CollectDeps

/-- Collect all constant names occurring in `e`. -/
def collectDeps (e : Expr) : Array Name :=
  e.foldConsts #[] fun
    | nm, acc => acc.push nm

end GenDecls.CollectDeps
