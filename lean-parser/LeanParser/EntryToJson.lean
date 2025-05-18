import Lean.Data.Json
open Lean Json

namespace GenDecls.EntryToJson

def entryToJson (id : Name) (kind : String)
    (prereqs cons : Array Name) : Json :=
  mkObj
    [ ("id",           str (toString id))
    , ("kind",         str kind)
    , ("prerequisites", Json.arr (prereqs.map (fun n => str (toString n))))
    , ("consequences",  Json.arr (cons.map   (fun n => str (toString n))))
    ]

end GenDecls.EntryToJson
