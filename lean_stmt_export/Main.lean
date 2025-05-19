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
def main (args : List String) : IO Unit := do
  -- Initialize Lean's search path to find standard library modules like 'Init'
  try
    Lean.initSearchPath (← Lean.findSysroot)
  catch ex =>
    IO.eprintln s!"Failed to initialize search path: {ex}"
    -- Decide if you want to exit here or try to continue
    -- For 'Init' not found, it's likely fatal, so rethrow or exit
    throw ex

  let file := args.headD "Main.lean" -- Consider if this default is appropriate for your tool's usage
  IO.println s!"Processing file: {file}" -- Added for debugging

  let input ← IO.FS.readFile file
  let opts := {} -- These are elaboration options, not search path configurations

  -- Elaborate the file and get its environment in IO
  -- The 'Main' here is a placeholder for the module name being compiled by runFrontend
  let (env, success) ← Lean.Elab.runFrontend input opts file `Main
  unless success do
    IO.eprintln "Elaboration failed"
    IO.Process.exit 1 -- Exit with an error code

  -- Now env : Environment is available in IO
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
