import Lean
import Lean.Data.Json
import Lean.Data.NameMap                  -- for `{}`-literals on NameMap
import LeanStmtExport.ExampleCapture

open Lean System

def gatherPrereqs (decls : Array ConstantInfo) : NameMap (Array Name) :=
  -- now `{}` works because of the EmptyCollection instance for NameMap
  decls.foldl {} fun m cinfo =>
    m.insert cinfo.name (cinfo.getUsedConstantsAsSet.toArray)

def invertGraph (m : NameMap (Array Name)) : NameMap (Array Name) :=
  -- use the top-level RBMap.fold (not a non-existent `.fold` method)
  Lean.RBMap.fold (fun outMap name deps =>
    deps.foldl outMap fun mm dep =>
      let arr := mm.findD dep #[]
      mm.insert dep (arr.push name)
  ) {} m

def main (args : List String) : IO Unit := do
  let root      := args.headD "."
  let allFiles  ← FilePath.walkDir root (fun _ => pure true)
  let leanFiles := allFiles.filter (·.extension == "lean")
  -- convert file paths to module Names
  let moduleNames := leanFiles.map fun f =>
    let pathStr := String.intercalate (toString FilePath.pathSeparator) f.components
    -- drop “.lean” and replace separators with “.”
    Name.mkString Name.anonymous (pathStr.trimDropExtension.replaceSep ".")
  let env ← Lean.Core.withImportModules moduleNames getEnv

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
