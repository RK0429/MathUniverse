/-
Copyright (c) 2025 MathUniverse.
Released under Apache 2.0 license.
-/
import Lean
import Lean.Meta
import Lean.Elab.Command
import Std.Data.HashSet
import Lean.Data.Json

/-!
# ExportDeps

Summary:
Extract all declarations (axioms, definitions, theorems, examples, inductive types, etc.) from the environment,
and collect their dependencies (constant usages in types and values).

Notations:
- `declKind` returns the kind of a declaration via `ci.kind`.
- `collectConstsInExpr` traverses expressions to gather referenced constants.
- `getDeclInfo` assembles name, kind, and dependencies.
- `export_deps` command writes JSON to `export_deps.json`.

Tags: export, dependencies, analysis
-/

namespace ExportDeps

open Lean
open Lean.Meta
open Lean.Elab.Command
open Std

/-!
Classify the kind of a declaration.
-/
def declKind (ci : ConstantInfo) : String :=
  match ci with
  | ConstantInfo.defnInfo _   => "def"
  | ConstantInfo.thmInfo _    => "theorem"
  | ConstantInfo.axiomInfo _  => "axiom"
  | ConstantInfo.opaqueInfo _ => "opaque"
  | ConstantInfo.inductInfo _ => "inductive"
  | _                         => "other"

/--
Recursively collect constant names in an expression.
-/
partial def collectConstsInExpr (e : Expr) (acc : HashSet Name := {}) : HashSet Name :=
  match e with
  | Expr.const n _           => acc.insert n
  | Expr.app f a             => collectConstsInExpr f (collectConstsInExpr a acc)
  | Expr.lam _ _ b _         => collectConstsInExpr b acc
  | Expr.forallE _ _ b _     => collectConstsInExpr b acc
  | Expr.letE _ _ val body _ => collectConstsInExpr val (collectConstsInExpr body acc)
  | Expr.mdata _ b           => collectConstsInExpr b acc
  | Expr.proj _ _ b          => collectConstsInExpr b acc
  | _                        => acc

/--
Holds extracted information about a declaration.
-/
structure DeclInfo where
  name : Name
  kind : String
  deps : List Name

instance : ToJson DeclInfo where
  toJson di :=
    let depsArr := di.deps.toArray.map fun n => Json.str n.toString
    Json.mkObj [ ("name", Json.str di.name.toString)
               , ("kind", Json.str di.kind)
               , ("deps", Json.arr depsArr) ]

/--
Extract `DeclInfo` for a given ConstantInfo.
-/
def getDeclInfo (ci : ConstantInfo) : DeclInfo :=
  let typeDeps := (collectConstsInExpr ci.type {}).toList
  let valDeps := match ci.value? with
    | some v => (collectConstsInExpr v {}).toList
    | none   => []
  let deps := (typeDeps ++ valDeps).eraseDups
  { name := ci.name, kind := declKind ci, deps := deps }

/-!
Command `export_deps` prints all declaration infos as JSON to stdout.
-/
elab "export_deps" : command => do
  let env ← getEnv
  let infos := env.constants.toList.toArray.map fun (_, ci) => getDeclInfo ci
  let json := Json.arr (infos.map ToJson.toJson)
  liftIO $ IO.println (json.pretty 2)
  logInfo m! "Printed {infos.size} declarations as JSON"

end ExportDeps
