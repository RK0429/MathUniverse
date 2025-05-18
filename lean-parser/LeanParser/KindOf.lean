import Mathlib.Lean.Expr.Basic  -- for toDeclaration!
open Lean

namespace GenDecls.KindOf

def kindOf (cinfo : ConstantInfo) : String :=
  match cinfo.toDeclaration! with
  | Declaration.axiomDecl _          => "axiom"
  | Declaration.defnDecl  _          => "definition"
  | Declaration.thmDecl   _          => "theorem"
  | Declaration.opaqueDecl _         => "opaque"
  | _                                 => "other"

end GenDecls.KindOf
