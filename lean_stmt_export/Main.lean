/-
Main.lean

This file aggregates all declarations (axioms, definitions, theorems, inductives, etc.) and recorded example dependencies from the environment, and outputs them as structured JSON.
-/

import Lean
import Lean.Data.Json
import LeanStmtExport.ExampleCapture
import LeanStmtExport.ExportDeps
import Lean.Elab.Command
import Lean.Elab.Frontend

open Lean
open ExportDeps
open LeanStmtExport.ExampleCapture

/--
Main entry point: gather declaration infos and recorded example dependencies,
and then print them as structured JSON.
-/
def main (args : List String) : IO Unit := do
  -- 1. Allow `initialize` blocks to run (for any builtins)
  Lean.enableInitializersExecution
  -- 2. Discover the Lean sysroot (where the stdlib .olean files live)
  let sysroot ← IO.ofExcept Lean.findSysroot?
  -- 3. Populate Lean.searchPathRef from the sysroot and LEAN_PATH
  Lean.initSearchPath sysroot
  -- 4. Now you can elaborate files
  let input ← IO.FS.readFile (args.headD "Main.lean")
  let (env, success) ← Lean.Elab.runFrontend input {} "Main.lean" `Main
  unless success do
    IO.eprintln "Elaboration failed"
    return

  -- Now `env : Environment` is available in IO
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

  -- Print to stdout
  IO.println (resultJson.pretty 2)
