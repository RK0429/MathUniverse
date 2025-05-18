import Lean
import Lean.Data.Json
open Lean
open Lean.Environment

def main : IO Unit := do
  -- Run environment import and collect declarations
  Lean.withImportModules #[`Lean] {} (trustLevel := 1024) fun env => do
    let declInfos := collectDecls env
    let json := Lean.Json.arr (declInfos.map toJson)
    IO.FS.writeFile "declarations.json" (json.pretty)
    IO.println s!"Exported {declInfos.size} declarations."

def collectDecls (env : Environment) : Array ConstantInfo :=
  -- Convert environment constants to a list of ConstantInfo
  env.constants.toList.foldl (fun acc entry => acc.push entry.2) #[]

instance : ToJson ConstantInfo where
  toJson c := Lean.Json.mkObj
    [ ("name", toJson c.name)
    , ("type", toJson c.type)
    , ("value?", toJson c.value?) ]
