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

def constantKindToString : ConstantKind → String
  | ConstantKind.axiom     => "axiom"
  | ConstantKind.defn      => "definition"
  | ConstantKind.opaque    => "opaque"
  | ConstantKind.thm       => "theorem"
  | ConstantKind.ctor      => "constructor"
  | ConstantKind.induct    => "inductive"
  | ConstantKind.rec       => "recursor"

-- Helper function to convert FilePath to module Name
def moduleNameOf (rootPath : FilePath) (filePath : FilePath) : Name :=
  let normFilePathToString := filePath.normalize.toString
  let normRootPathString := rootPath.normalize.toString

  let prefix :=
    if normRootPathString == "." then
      ""
    else
      normRootPathString ++ System.FilePath.pathSeparator.toString

  let relPathString :=
    if normFilePathToString.startsWith prefix then
      normFilePathToString.drop prefix.length
    else
      (filePath.fileStem.getD "") ++ (filePath.extension.getD "")

  let modPathWithoutExt := (FilePath.mk relPathString).withExtension ""
  Name.mkFromComponents (modPathWithoutExt.components.filter fun c => c != "." && !c.isEmpty)

def main (args : List String) : IO Unit := do
  let root     := FilePath.mk (args.headD ".")
  let allFiles ← FilePath.walkDir root -- Removed `fun _ => pure true` as it's the default
  let leanFiles := allFiles.filter fun f => f.extension == some ".lean"

  -- 1) Correctly build Array Name for modules
  let moduleNames := leanFiles.map (moduleNameOf root)

  -- 2) Import all modules and get the environment correctly
  let imports := moduleNames.map fun name => { module := name : Import }
  let envResult ← Lean.withImportModules imports (opts := {}) (trustLevel := 0) getEnv

  let env ← match envResult with
    | Except.ok e => pure e
    | Except.error err => IO.throwServerError s!"Failed to import modules and get environment: {err}"

  let exampleMap ← LeanStmtExport.ExampleCapture.readExampleMap
  let decls       := (env.constants.toList.map Prod.snd).toArray
  let prereqMap   := gatherPrereqs decls

  let mergedMap := Lean.RBMap.fold (fun m k xs =>
    let old := m.findD k #[]
    m.insert k (old ++ xs)
  ) prereqMap exampleMap

  let consMap := invertGraph mergedMap

  let infosList := (mergedMap.toList.map Prod.fst).map fun nm =>
    let kind := match env.find? nm with
      | some cinfo => ConstantKind.ofConstantInfo cinfo
      | none       => ConstantKind.axiom -- Or handle as an error/skip if a name from mergedMap isn't in env
    StatementInfo.mk
      nm.toString
      (constantKindToString kind)
      ((prereqMap.findD nm #[]).map toString)
      ((consMap.findD nm #[]).map toString)

  let infosJson := toJson infosList
  IO.FS.writeFile (root / "stmt_deps.json") (Lean.Json.pretty infosJson)
