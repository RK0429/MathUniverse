import Lean
import Lean.Data.Json
import Lean.Data.SMap
import Mathlib.Lean.Expr.Basic
import LeanParser.Map
import LeanParser.EntryToJson
import LeanParser.KindOf
import LeanParser.CollectDeps

open Lean Json
open LeanParser.Map
open LeanParser.EntryToJson
open LeanParser.KindOf
open LeanParser.CollectDeps

def main : IO Unit := do
  let env      ← importModules (imports := #[{ module := `Init, importAll := true }])
  let prMap    := buildPrereqMap env
  let consMap  := invertMap prMap
  let entries  := prMap.toArray.map fun (id, prereqs) =>
    let kind := kindOf (env.find? id).get!
    let cons := consMap.findD id #[]
    entryToJson id kind prereqs cons
  let json := Json.arr entries
  IO.FS.writeFile "statements.json" (json.pretty)
  IO.println s!"Exported {entries.size} statements."
