# Lean Parser

## Overview

The **lean\_stmt\_export** package scans a Lean 4 project, loads every module into a single `Environment`, and emits a JSON array of **all** statements—including `axiom`, `def`, `theorem`/`lemma`, **and** `example` blocks—with for each:

* **`id`**: fully qualified name (string)
* **`kind`**: one of `"axiom"`, `"defn"`, `"thm"`, `"opaque"`, `"induct"`, `"ctor"`, `"recursor"`, **or** `"example"`
* **`prerequisites`**: array of constant names it refers to
* **`consequences`**: array of statement IDs that refer to it

It can be invoked as a **CLI executable** or integrated as a **Lake plugin**.

---

## 1. File Traversal & Module Loading

1. **Collect `.lean` files**

   ```lean
   let files ← System.FilePath.walkDir rootDir (fun _ => pure true)
   let leanFiles := files.filter (·.extension == ".lean")
   ```

2. **Derive module names**
   Strip `rootDir` prefix and replace path separators with dots:

   ```lean
   let moduleNames := leanFiles.map (fun f => 
     (f.dropPrefix rootDir).toString.trimDropExtension.replaceSep "."
   )
   ```

3. **Build unified environment**

   ```lean
   let env ← Lean.Core.withImportModules moduleNames (init := {}) fun _ => getEnv
   ```

   This runs in `MetaM`, imports every module, and executes initializers.

---

## 2. Capturing `example` Statements

Lean's `example` command does **not** produce a `ConstantInfo`. To include them:

1. **Register a command elaborator**
   In `ExampleCapture.lean`:

   ```lean
   import Lean

   open Lean Elab Command

   syntax (name := exampleCommand) "example" term : command

   @[command_elab exampleCommand] def elabExample : CommandElab := fun stx => do
     -- 1. Elaborate the term to get its Expr
     let termExpr ← Term.elabTerm stx[1] none
     let consts ← pure (termExpr.getUsedConstantsAsSet.toArray)
     -- 2. Generate a fresh synthetic name for this example
     let exName ← mkFreshUserName `example
     -- 3. Record it in a global IORef or pass into the final JSON collector
     recordExample exName consts
   ```

2. **Accumulating examples**
   Maintain an `IO.Ref` or `NameMap` of:

   ```lean
   NameMap (Array Name)  -- maps synthetic example names → dependencies
   ```

3. **Merge with `env.constants`** in the final export.

---

## 3. Declaration Extraction, Classification & Prerequisites

1. **Gather all real declarations**

   ```lean
   let decls := env.constants.values
   ```

2. **Build a prerequisites map**

   ```lean
   def gatherPrereqs (decls : Array ConstantInfo) : NameMap (Array Name) :=
     decls.foldl (init := {}) fun m cinfo =>
       m.insert cinfo.name cinfo.getUsedConstantsAsSet.toArray
   ```

3. **Include synthetic examples**

   ```lean
   let prereqMap := (gatherPrereqs decls).merge exampleMap (fun _ realDeps exDeps =>
     realDeps ++ exDeps
   )
   ```

---

## 4. Building Consequences

Invert `prereqMap` to get, for each name, the list of statements that depend on it:

```lean
def invertGraph (m : NameMap (Array Name)) : NameMap (Array Name) :=
  m.fold (init := {} : NameMap (Array Name)) fun outMap name deps =>
    deps.foldl (init := outMap) fun mm dep =>
      let arr := mm.findD dep #[]
      mm.insert dep (arr.push name)

let consMap := invertGraph prereqMap
```

---

## 5. JSON Serialization

Define the schema:

```lean
structure StatementInfo where
  id            : String
  kind          : String
  prerequisites : Array String
  consequences  : Array String
deriving ToJson
```

Produce the full array:

```lean
let allNames := (prereqMap.toList.map Prod.fst) |>.toArray
let infos := allNames.map fun nm =>
  let kind := match env.find? nm with
    | some cinfo => ConstantKind.ofConstantInfo cinfo
    | none       => -- synthetic example
      if exampleMap.contains nm then ConstantKind.example else ConstantKind.unknown
  { id            := nm.toString
  , kind          := kind.toString
  , prerequisites := prereqMap.findD nm #[].map toString
  , consequences  := consMap.findD nm #[].map toString
  }
IO.FS.writeFile (root / "stmt_deps.json") (Json.pretty! infos)
```

---

## 6. Updated `Main.lean` Sketch

```lean
import Lean
import Lean.Data.Json
import ExampleCapture  -- registers the example elaborator

open Lean Meta System

def main (args : List String) : IO Unit := do
  let root         := args.headD "."  
  let allFiles     ← FilePath.walkDir root (fun _ => pure true)
  let leanFiles    := allFiles.filter (·.extension == ".lean")
  let moduleNames  := leanFiles.map (fun f => 
                       (f.dropPrefix root).toString.trimDropExtension.replaceSep ".")
  let env          ← Core.withImportModules moduleNames (init := {}) fun _ => getEnv
  let decls        := env.constants.values
  let realPre      := gatherPrereqs decls
  let exampleMap   ← readExampleMap      -- from ExampleCapture's IO.Ref
  let prereqMap    := realPre.merge exampleMap (· ++ ·)
  let consMap      := invertGraph prereqMap
  let allNames     := (prereqMap.toList.map Prod.fst) |>.toArray
  let infos        := allNames.map fun nm =>
    let kind := match env.find? nm with
      | some cinfo => ConstantKind.ofConstantInfo cinfo
      | none       => ConstantKind.example
    { id            := nm.toString
    , kind          := kind.toString
    , prerequisites := prereqMap.findD nm #[].map toString
    , consequences  := consMap.findD nm #[].map toString
    }
  IO.FS.writeFile (root / "stmt_deps.json") (Json.pretty! infos)
```

---

## 7. Final JSON Schema Example

```json
[
  {
    "id": "Test.foo",
    "kind": "defn",
    "prerequisites": ["Nat.add", "Nat.succ"],
    "consequences": ["Test.foo_add", "Test.foo_example"]
  },
  {
    "id": "Test.foo_add",
    "kind": "thm",
    "prerequisites": ["Test.foo", "Eq.refl"],
    "consequences": []
  },
  {
    "id": "example_1",
    "kind": "example",
    "prerequisites": ["Test.foo", "Nat.succ"],
    "consequences": []
  }
]
```

This design leverages Lean 4's standard filesystem IO, metaprogramming API, and JSON serialization to deliver a turnkey tool for dependency analysis in formal developments.
