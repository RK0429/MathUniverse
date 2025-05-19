/-
Main.lean

This file aggregates all declarations (axioms, definitions, theorems, inductives, etc.) and recorded example dependencies from the environment, and outputs them as structured JSON.
-/

import Lean
import Lean.Data.Json
import LeanStmtExport.ExampleCapture
import LeanStmtExport.ExportDeps
import Lean.Elab.Command

open Lean
open ExportDeps
open LeanStmtExport.ExampleCapture

/--
Main entry point: gather declaration infos and recorded example dependencies,
and then print them as pretty JSON.
-/
def main : IO Unit := Lean.run do
  -- Gather declaration infos
  let env ← getEnv
  let declInfos := env.constants.toList.toArray.map fun (_, ci) => getDeclInfo ci
  let declsJson := Json.arr (declInfos.map ToJson.toJson)

  -- Gather recorded examples
  let exampleMap ← readExampleMap
  let examplePairs := exampleMap.toList.toArray
  let examplesJsonArr := examplePairs.map fun (name, deps) =>
    let depsJsonArr := deps.map fun n => Json.str n.toString
    Json.mkObj [("name", Json.str name.toString), ("deps", Json.arr depsJsonArr)]
  let examplesJson := Json.arr examplesJsonArr

  -- Combine into final JSON object
  let resultJson := Json.mkObj [("declarations", declsJson), ("examples", examplesJson)]

  liftIO $ IO.println (resultJson.pretty 2)
