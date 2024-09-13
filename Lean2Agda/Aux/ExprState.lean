import Lean2Agda.Data.Value
import Lean2Agda.Data.Monad
import Lean2Agda.Aux.HygienicNames

import Std.Data.HashMap.Basic
import Lean.Message

open Std (HashMap)
open Lean (Name MessageData)

structure ExprState where
  hygienicNames: HygienicNames := {}
  patternNames: HashMap String Nat := {}
  bvarValues : Array String := {}
  deriving Inhabited

genSubMonad (ExprState) (HygienicNames) hygienicNames hygienicNames

variable [Value Language]

section
local macro "M": term => `(Except MessageData)

def withLocalName
  (name : Name) (pattern: Bool): M (SubState ExprState String) :=
  go name false
where
  go (n: Name) (inside: Bool): M (SubState ExprState String) :=
    match n with
    | .anonymous =>
      if inside then
        throw m!"unexpected local name {name}"
      else
        pure <| SubState.mkPure "_"
    | .str Name.anonymous v => do
      if inside then
        throw m!"unexpected local name {name}"
      else if pattern then
        let enter := λ ({bvarValues, patternNames, hygienicNames}: ExprState) ↦
          let h := patternNames.getD v 0
          let i := s!"{stringifyIdent v}{if h == 0 then "" else if h == 1 then "#" else s!"#{h - 1}"}"
          ((i, h), ({patternNames := patternNames.insert v (h + 1), bvarValues, hygienicNames}: ExprState))
        let exit := λ h ({bvarValues, patternNames, hygienicNames}: ExprState) ↦
          ({bvarValues, hygienicNames, patternNames :=
            (if h == 0 then
              patternNames.erase v
            else
              patternNames.insert v h)
          } : ExprState)
        pure <| SubState.mk enter exit
      else
        pure <| SubState.mkPure (stringifyIdent v)
    | .str v "_@" => do
      let v := s!"{v}"
      pure <| makeHygienicName v
    | .str n _ => go n true
    | .num n _ => go n true

def bindStr' (n: String): SubState ExprState String :=
  let enter := λ {bvarValues, patternNames, hygienicNames} ↦ ((n, ()), {bvarValues := bvarValues.push n, patternNames, hygienicNames})
  let exit := λ _ {bvarValues, patternNames, hygienicNames} ↦ {bvarValues := bvarValues.pop, patternNames, hygienicNames }
  SubState.mk enter exit

def bindIf' (pattern: Bool) (n: Name): M (SubState ExprState String) := do
  pure <| (← withLocalName n pattern).compose bindStr'

def bind' (n: Name): M (SubState ExprState String) :=
  -- TODO: implement proper name liveness analysis
  --bindIf false n e
  bindIf' true n
end
