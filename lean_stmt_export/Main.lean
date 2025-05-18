import Lean
import Lean.CoreM
import Lean.Data.Json
import Lean.Data.NameMap                  -- for `{}`-literals on NameMap
import LeanStmtExport.ExampleCapture

open Lean System

structure StatementInfo where
  id            : String
  kind          : String
  prerequisites : Array String
  consequences  : Array String
deriving ToJson

def gatherPrereqs (decls : Array ConstantInfo) : NameMap (Array Name) :=
  decls.foldl (init := {}) fun m cinfo =>
    m.insert cinfo.name (cinfo.getUsedConstantsAsSet.toArray)

def invertGraph (m : NameMap (Array Name)) : NameMap (Array Name) :=
  m.fold (init := {}) fun outMap name deps =>
    deps.foldl (init := outMap) fun mm dep =>
      mm.insert dep ((mm.findD dep #[]).push name)

def main (args : List String) : IO Unit := do
  let root := FilePath.mk (args.headD ".")
  let allFiles ← FilePath.walkDir root (fun _ => pure true)
  let leanFiles := allFiles.filter fun f => f.extension == some ".lean"
  -- convert file paths to module Names
  let moduleNames := leanFiles.map fun f =>
    Name.mkStr Name.anonymous (toString f)
  let env ← withImportModules moduleNames getEnv

  let exampleMap ← LeanStmtExport.ExampleCapture.readExampleMap
  let prereqMap  := gatherPrereqs env.constants.values
  -- merge exampleMap into prereqMap using RBMap.fold
  let mergedMap  := Lean.RBMap.fold (fun m k xs =>
    let old := m.findD k #[]
    m.insert k (old ++ xs)
  ) prereqMap exampleMap
  let consMap    := invertGraph mergedMap

  -- build the list of JSON-serializable infos
  let infosList := (mergedMap.toList.map Prod.fst).map fun nm =>
    let kind := match env.find? nm with
      | some cinfo => ConstantKind.ofConstantInfo cinfo
      | none       => ConstantKind.axiom
    { id            := nm.toString
    , kind          := kind.toString
    , prerequisites := prereqMap.findD nm #[] |>.map toString
    , consequences  := consMap.findD nm #[] |>.map toString
    }
  let infosJson := toJson infosList
  IO.FS.writeFile (root / "stmt_deps.json") (Lean.Json.pretty infosJson)
