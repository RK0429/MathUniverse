import Lean
import Lean.Data.Json
import LeanStmtExport.ExampleCapture
import LeanStmtExport.ExportDeps
import Lean.Elab.Command
import Lean.Util.Path

open Lean
open ExportDeps
open LeanStmtExport.ExampleCapture
open System

/--
Parses the JSON output of `lake print-paths` to get the lean search paths.
-/
def getLeanPathFromLakeOutput (lakeOutput : String) : IO (List FilePath) := do
  match Json.parse lakeOutput with
  | Except.error err => throw <| IO.userError s!"Failed to parse lake print-paths output: {err}"
  | Except.ok json =>
    match json.getObjVal? "leanPath" with
    | Except.error err => throw <| IO.userError s!"'leanPath' not found in lake print-paths output: {err}"
    | Except.ok leanPathJson =>
      match leanPathJson.getArr? with
      | Except.error err => throw <| IO.userError s!"'leanPath' is not an array: {err}"
      | Except.ok arr =>
        let paths ← arr.mapM fun pJson =>
          match pJson.getStr? with
          | Except.error err => throw <| IO.userError s!"Path in 'leanPath' is not a string: {err}"
          | Except.ok pStr => pure (FilePath.mk pStr)
        return paths.toList

/--
Gets the LEAN_PATH for a given Lake project directory by running `lake print-paths`.
-/
def getLeanPathForProject (projectDir : FilePath) : IO (List FilePath) := do
  IO.println s!"Querying LEAN_PATH for project: {projectDir}"
  -- Ensure the target project is built (optional, but good practice)
  let buildProc ← IO.Process.output {
    cmd := "lake"
    args := #["build"]
    cwd := projectDir -- Run 'lake build' in the target project's directory
  }
  if buildProc.exitCode != 0 then
    IO.eprintln s!"Failed to build target project {projectDir}: {buildProc.stderr}"
    -- Decide if you want to throw an error or continue

  let proc ← IO.Process.output {
    cmd := "lake"
    args := #["print-paths"]
    cwd := projectDir -- Run 'lake print-paths' in the target project's directory
  }
  if proc.exitCode != 0 then
    throw <| IO.userError s!"'lake print-paths' failed for project {projectDir}: {proc.stderr}"
  getLeanPathFromLakeOutput proc.stdout

def main (args : List String) : IO Unit := do
  if args.length < 2 then
    IO.eprintln "Usage: lean_stmt_export <path_to_target_project_root> <path_to_lean_file_to_process>"
    IO.Process.exit 1

  let targetProjectDir := FilePath.mk args[0]!
  let fileToProcess := FilePath.mk args[1]!

  IO.println s!"Target project directory: {targetProjectDir}"
  IO.println s!"Processing file: {fileToProcess}"

  let targetProjectLeanPath : List FilePath ← getLeanPathForProject targetProjectDir -- Renamed for clarity

  try
    -- Initialize Lean's search path with the paths from the target project.
    -- This will include the target project's build artifacts and its dependencies.
    let sysroot ← Lean.findSysroot -- Get the system root for the current Lean installation
    IO.println s!"Using Lean sysroot: {sysroot}"
    IO.println s!"Using search paths from target project: {targetProjectLeanPath.map toString}"
    Lean.initSearchPath sysroot targetProjectLeanPath -- Pass the List FilePath directly

  catch ex =>
    IO.eprintln s!"Failed to initialize search path for target project: {ex}"
    throw ex

  let input ← IO.FS.readFile fileToProcess
  let opts := {} -- Consider if you need specific Elab.Options

  -- The module name for runFrontend can often be derived or set to a placeholder.
  -- For a file like `../universe/Universe/Group.lean`, the module name might be `Universe.Group`.
  -- Deriving this robustly might require more logic based on `targetProjectDir` and `fileToProcess`.
  let moduleName : Name ← match ←Lean.moduleNameOfFileName fileToProcess (some targetProjectDir) with
    | some name => pure name
    | none => throw <| IO.userError s!"Could not determine module name for file {fileToProcess} relative to root {targetProjectDir}"
  IO.println s!"Elaborating with module name: {moduleName}"

  let (env, success) ← Lean.Elab.runFrontend input opts fileToProcess.toString moduleName
  unless success do
    IO.eprintln "Elaboration failed"
    IO.Process.exit 1

  let declInfos := env.constants.toList.toArray.map fun (_, ci) => getDeclInfo ci
  let declsJson := Json.arr (declInfos.map ToJson.toJson)

  let exampleMap ← readExampleMap
  let examplePairs := exampleMap.toList.toArray
  let examplesJsonArr := examplePairs.map fun (name, deps) =>
    let depsJsonArr := deps.map fun n => Json.str n.toString
    Json.mkObj [("name", Json.str name.toString), ("deps", Json.arr depsJsonArr)]
  let examplesJson := Json.arr examplesJsonArr

  let resultJson := Json.mkObj [("declarations", declsJson), ("examples", examplesJson)]
  IO.println (resultJson.pretty 2)
