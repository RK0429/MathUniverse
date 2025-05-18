import Lean
import Lean.Data.SMap
import Std.Data.HashMap
import LeanParser.CollectDeps
import Mathlib.Lean.Expr.Basic

open Lean
open Std
open LeanParser.CollectDeps

namespace LeanParser.Map

def buildPrereqMap (env : Environment) : HashMap Name (Array Name) :=
  env.constants.fold (init := mkHashMap) fun m _ cinfo =>
    let decl   := cinfo.toDeclaration!
    let depsT  := collectDeps decl.type
    let depsV  := depsT ++ collectDeps decl.value?.getD default
    m.insert cinfo.name depsV

def invertMap (prMap : HashMap Name (Array Name)) : HashMap Name (Array Name) :=
  prMap.fold (init := mkHashMap) fun consMap id deps =>
    deps.foldl (fun cm dep =>
      let old := cm.findD dep #[]
      cm.insert dep (old.push id)
    ) consMap

end GenDecls.Map
