# Lean Parser

Here’s a concrete design for a Lean 4 package—let’s call it **lean_stmt_export**—that walks a directory of `.lean` files, builds a unified environment, and emits JSON describing each statement’s ID, kind, and dependencies.

In summary, the package uses `System.FilePath.walkDir` and `IO.FS` to find all source files recursively ([loogle.lean-lang.org](https://loogle.lean-lang.org/?q=IO)), loads them into a single `Environment` via `Lean.Core.withImportModules` in the `MetaM` monad , iterates over `env.constants.values` to collect every `ConstantInfo` , classifies each via `ConstantKind.ofConstantInfo` , extracts referenced names with `ConstantInfo.getUsedConstantsAsSet` , and finally serializes an array of `{ id, kind, deps }` objects using `Lean.Data.Json`’s `ToJson` machinery.

## Overview

The **lean_stmt_export** package provides both a CLI executable and an optional Lake plugin to analyze Lean 4 projects . It outputs a JSON array where each entry has:

- **id**: the fully qualified `Name` of the declaration
- **kind**: one of `"axiom"`, `"defn"`, `"thm"`, `"opaque"`, etc.
- **deps**: an array of strings naming every other constant it references .

## 1. File Traversal & Module Loading

1. **Collect files**

    ```lean
    let files ← System.FilePath.walkDir rootDir
      (fun _ => pure true)   -- visit all subdirectories
    let leanFiles := files.filter (·.extension == ".lean")
    
    ```

    Uses `walkDir : FilePath → (FilePath → IO Bool) → IO (Array FilePath)` ([loogle.lean-lang.org](https://loogle.lean-lang.org/?q=IO)).

2. **Derive module names**

    Drop the project-root prefix and replace path separators with dots to get Lean module names.

3. **Build environment**

    ```lean
    let env ← Lean.Core.withImportModules moduleNames
      (init := {})          -- start from empty
      fun _ => getEnv
    
    ```

    Runs in the `MetaM` monad to import every module and execute initializers .

## 2. Declaration Extraction & Classification

1. **Gather all declarations**

    ```lean
    let decls := env.constants.values
    
    ```

    `env.constants : SMap Name ConstantInfo` holds every kernel-checked declaration .

2. **Classify each**

    ```lean
    let kind := ConstantKind.ofConstantInfo cinfo
    
    ```

    Distinguishes constructors for `axiomInfo`, `defnInfo`, `thmInfo`, `opaque`, `inductInfo`, etc. .

## 3. Dependency Analysis

For each `cinfo : ConstantInfo`:

```lean
let depsSet := cinfo.getUsedConstantsAsSet
let depsArray := depsSet.toArray.map toString

```

`getUsedConstantsAsSet` traverses both the type and the body to collect every constant name . Converting to `String` ensures JSON compatibility .

## 4. JSON Serialization

Define a data structure:

```lean
structure StatementInfo where
  id   : String
  kind : String
  deps : Array String
deriving ToJson

```

Using `deriving ToJson` (and `FromJson` if desired) lets Lean auto-generate conversion routines . Then:

```lean
let infos : Array StatementInfo := decls.map fun cinfo =>
  { id := cinfo.name.toString
  , kind := (ConstantKind.ofConstantInfo cinfo).toString
  , deps := (cinfo.getUsedConstantsAsSet.toArray.map toString)
  }
let jsonOut := Json.pretty! infos
IO.println jsonOut

```

`Json.pretty!` comes from `Lean.Data.Json.Printer` and produces a well-formatted JSON string .

## 5. Putting It All Together

Below is a sketch of `Main.lean` in the package’s `src` directory:

```lean
import Lean
import Lean.Data.Json
open Lean Meta System

def main (args : List String) : IO Unit := do
  let root := args.headD "."    -- project root
  let files ← System.FilePath.walkDir root (fun _ => pure true)
  let mods  := files.filter (·.extension == ".lean")
                 |>.map (fun f => -- derive module name)
  let env ← Core.withImportModules mods (init := {}) fun _ => getEnv
  let decls := env.constants.values
  let infos := decls.map fun cinfo =>
    { id   := cinfo.name.toString
    , kind := (ConstantKind.ofConstantInfo cinfo).toString
    , deps := (cinfo.getUsedConstantsAsSet.toArray.map toString)
    }
  IO.FS.writeFile (root / "stmt_deps.json") (Json.pretty! infos)

```

## JSON Schema

```json
[
  {
    "id":   "Math.Universe.Defs.myTheorem",
    "kind": "thm",
    "deps": ["Nat.zero", "Nat.succ", "MyLemma"]
  },
  …
]

```

This design leverages Lean 4’s standard filesystem IO, metaprogramming API, and JSON serialization to deliver a turnkey tool for dependency analysis in formal developments.
