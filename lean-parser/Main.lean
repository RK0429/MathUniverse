import Lean
import Lean.Data.Json
import LeanParser.ExampleCapture

open Lean System

def gatherPrereqs (decls : Array ConstantInfo) : NameMap (Array Name) :=
  decls.foldl (init := {}) fun m cinfo =>
    m.insert cinfo.name (cinfo.getUsedConstantsAsSet.toArray)


def invertGraph (m : NameMap (Array Name)) : NameMap (Array Name) :=
  m.fold (init := {} : NameMap (Array Name)) fun outMap name deps =>
    deps.foldl (init := outMap) fun mm dep =>
      let arr := mm.findD dep #[]
      mm.insert dep (arr.push name)


def main (args : List String) : IO Unit := do
  let root := args.headD "."
  let allFiles ← FilePath.walkDir root (fun _ => pure true)
  let leanFiles := allFiles.filter (·.extension == "lean")
  let moduleNames := leanFiles.map fun f =>
    (f.dropPrefix root).toString.trimDropExtension.replaceSep "."
  let env ← Lean.Core.withImportModules moduleNames (init := {}) fun _ => getEnv
  let exampleMap ← LeanParser.ExampleCapture.readExampleMap
  let prereqMap := (gatherPrereqs env.constants.values).merge exampleMap (· ++ ·)
  let consMap := invertGraph prereqMap
  let allNames := prereqMap.toList.map Prod.fst
  let infos := allNames.map fun nm =>
    let kind := match env.find? nm with
      | some cinfo => ConstantKind.ofConstantInfo cinfo
      | none       => ConstantKind.example
    { id            := nm.toString
    , kind          := kind.toString
    , prerequisites := (prereqMap.findD nm #[]).map toString
    , consequences  := (consMap.findD nm #[]).map toString
    }
  IO.FS.writeFile (root / "stmt_deps.json") (Json.pretty! infos)
