import Lean
import Lean.Data.Json
import LeanStmtExport.ExampleCapture
import LeanStmtExport.ExportDeps
import Lean.Elab.Command
import Lean.Util.Path -- Make sure this is imported for findSysroot, initSearchPath, moduleNameOfFileName

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
Gets the LEAN_PATH for a given Lake project directory by running `lake env print-paths --json`.
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
    -- Decide if you want to throw an error or continue if build fails but paths might still be available

  let proc ← IO.Process.output {
    cmd := "lake"
    args := #["env", "print-paths", "--json"] -- Changed this line
    cwd := projectDir -- Run 'lake env print-paths --json' in the target project's directory
  }
  if proc.exitCode != 0 then
    -- Update the error message to reflect the new command
    throw <| IO.userError s!"'lake env print-paths --json' failed for project {projectDir}: {proc.stderr}"
  getLeanPathFromLakeOutput proc.stdout

-- Helper function to get a value from Option within IO, or throw a specific error
def getOrFail (optVal : Option α) (errorMsg : String) : IO α :=
  match optVal with
  | some val => pure val
  | none => throw <| IO.userError errorMsg

def main (args : List String) : IO Unit := do
  if args.length < 2 then
    IO.eprintln "Usage: lean_stmt_export <path_to_target_project_root> <path_to_lean_file_to_process>"
    IO.Process.exit 1

  let targetProjectDir := FilePath.mk args[0]!
  let fileToProcess := FilePath.mk args[1]!

  IO.println s!"Target project directory: {targetProjectDir}"
  IO.println s!"Processing file: {fileToProcess}"

  let targetProjectLeanPath : List FilePath ← getLeanPathForProject targetProjectDir

  try
    let sysroot ← Lean.findSysroot
    IO.println s!"Using Lean sysroot: {sysroot}"
    IO.println s!"Using search paths from target project: {targetProjectLeanPath.map toString}"
    Lean.initSearchPath sysroot targetProjectLeanPath
  catch ex =>
    IO.eprintln s!"Failed to initialize search path for target project: {ex}"
    throw ex

  let input ← IO.FS.readFile fileToProcess
  let opts := {}

  -- Step 1: Get the Option Name from the IO action
  let moduleNameOption ← Lean.moduleNameOfFileName fileToProcess (some targetProjectDir)

  -- Step 2: Use the helper to get Name or throw an error
  let moduleName ← getOrFail moduleNameOption s!"Could not determine module name for file {fileToProcess} relative to root {targetProjectDir}"

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
