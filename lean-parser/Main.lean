import Lean
import Lean.Core
import Lean.Elab.Module
import Lean.Data.Json
import LeanParser.ExampleCapture

open Lean System

def gatherPrereqs (decls : Array ConstantInfo) : NameMap (Array Name) :=
  decls.foldl {} fun m cinfo =>
    m.insert cinfo.name (cinfo.getUsedConstantsAsSet.toArray)

def invertGraph (m : NameMap (Array Name)) : NameMap (Array Name) :=
  m.fold {} fun outMap name deps =>
    deps.foldl outMap fun mm dep =>
      let arr := mm.findD dep #[]
      mm.insert dep (arr.push name)

def main (args : List String) : IO Unit := do
  let root := args.headD "."
  let allFiles ← FilePath.walkDir root (fun _ => pure true)
  let leanFiles := allFiles.filter (·.extension == "lean")
  -- convert to module names
  let moduleNames := leanFiles.map fun f =>
    let s := f.components.join s!"{System.FilePath.pathSeparator}"
    Name.mkString Name.anonymous (s.trimDropExtension.replaceSep ".")
  let env ← withImportModules moduleNames getEnv

  let exampleMap ← LeanParser.ExampleCapture.readExampleMap
  let prereqMap := gatherPrereqs env.constants.values
  let mergedMap := exampleMap.fold prereqMap fun m k xs =>
    let old := m.findD k #[]
    m.insert k (old ++ xs)
  let consMap := invertGraph mergedMap

  let infos := (mergedMap.toList.map Prod.fst).map fun nm =>
    let kind := match env.find? nm with
      | some cinfo => ConstantKind.ofConstantInfo cinfo
      | none       => ConstantKind.axiom
    { id            := nm.toString
    , kind          := kind.toString
    , prerequisites := prereqMap.findD nm #[] |>.map toString
    , consequences  := consMap.findD nm #[] |>.map toString
    }
  IO.FS.writeFile (root / "stmt_deps.json") (Lean.Json.pretty infos)
