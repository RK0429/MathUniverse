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

-- 1) Helper to convert ConstantKind → String
def constantKindToString : ConstantKind → String
  | ConstantKind.axiom     => "axiom"
  | ConstantKind.defn      => "definition"
  | ConstantKind.opaque    => "opaque"
  | ConstantKind.thm       => "theorem"
  | ConstantKind.ctor      => "constructor"
  | ConstantKind.induct    => "inductive"
  | ConstantKind.rec       => "recursor"

def main (args : List String) : IO Unit := do
  let root     := FilePath.mk (args.headD ".")
  let allFiles ← FilePath.walkDir root fun _ => pure true
  let leanFiles := allFiles.filter fun f => f.extension == some ".lean"

  -- 2) Build Array Name
  let moduleNames :=
    leanFiles.map fun f =>
      (toString f).toSubstring.dropExtension.toName

  -- 3) Import all modules and get the environment
  let env : Environment ←
    withImportModules moduleNames do
      getEnv

  let exampleMap ← LeanStmtExport.ExampleCapture.readExampleMap
  let decls       := (env.constants.toList.map Prod.snd).toArray
  let prereqMap   := gatherPrereqs decls

  -- ... rest of your code unchanged ...
  let mergedMap := Lean.RBMap.fold (fun m k xs =>
    let old := m.findD k #[]
    m.insert k (old ++ xs)
  ) prereqMap exampleMap

  let consMap := invertGraph mergedMap

  let infosList := (mergedMap.toList.map Prod.fst).map fun nm =>
    let kind := match env.find? nm with
      | some cinfo => ConstantKind.ofConstantInfo cinfo
      | none       => ConstantKind.axiom
    StatementInfo.mk
      nm.toString
      (constantKindToString kind)
      ((prereqMap.findD nm #[]).map toString)
      ((consMap.findD nm #[]).map toString)

  let infosJson := toJson infosList
  IO.FS.writeFile (root / "stmt_deps.json") (Lean.Json.pretty infosJson)
