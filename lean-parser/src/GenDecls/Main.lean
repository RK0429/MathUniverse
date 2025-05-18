import Lean
import Lean.Data.Json
open Lean

/-- Collect all ConstantInfo values from the environment. -/
def collectDecls (env : Environment) : Array ConstantInfo :=
  env.constants.fold (init := #[]) fun acc _ cinfo =>
    acc.push cinfo
  -- uses SMap.fold on `env.constants` :contentReference[oaicite:0]{index=0}

def main : IO Unit := do
  -- 1. Build a fresh environment importing the core Init module
  let env ← importModules (imports := #[
    { module := `Init, importAll := true }
  ]) {}
  -- `importModules` lives in `Lean` and returns IO Environment :contentReference[oaicite:1]{index=1}

  -- 2. Pull out all declarations
  let declInfos := collectDecls env

  -- 3. Turn into a JSON array
  let json := Json.arr (declInfos.map fun c =>
    Json.mkObj [
      ("name", Json.str (toString c.name)),
      ("type", Json.str (toString c.type))
    ]
  )
  -- use `Json.arr`+`Json.mkObj` from `Lean.Data.Json` :contentReference[oaicite:2]{index=2}

  -- 4. Write to file and report
  IO.FS.writeFile "declarations.json" (json.pretty)
  IO.println s!"Exported {declInfos.size} declarations."
