import Lean2Agda.Output.Language

variable {M: Type → Type} [Monad M]
  [MonadReaderOf Language M]

-- not including space or @.(){};_
-- TODO: handle identifiers conflicting with Agda defs
def stringifyIdent
  (s : String) : M String := do
  let s := s.foldl stringifyIdentAux ""
  pure <| if (← readThe Language).keywords.contains s then
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
