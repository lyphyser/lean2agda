import Lean2Agda.Data.Value
import Lean2Agda.Output.Language

variable  [Value Language]

-- not including space or @.(){};_
-- TODO: handle identifiers conflicting with Agda defs
def stringifyIdent
  (s : String) : String :=
  let s := s.foldl stringifyIdentAux ""
  if (valueOf Language).keywords.contains s then
    "`" ++ s ++ "`"
  else
    s
where stringifyIdentAux (acc : String) (c : Char) : String :=
  if c = '_' then
    acc ++ "-"
  else if c = '.' then
    acc ++ ":"
  else -- TODO: support ⟪⟫ escaped idents
    acc ++ String.singleton c
