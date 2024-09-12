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

variable {M: Type → Type} [Monad M] [MonadExceptOf MessageData M]
  [MonadStateOf ExprState M] [Value Language]

def withLocalName
  {α: Type} [Inhabited α] (name : Name) (pattern: Bool) (f: String → M α): M α :=
  go name false f
where
  go (n: Name) (inside: Bool) (f: String → M α): M α := do
    match n with
    | .anonymous =>
      if inside then
        throw m!"unexpected local name {name}"
      else
        f "_"
    | .str Name.anonymous v => do
      if inside then
        throw m!"unexpected local name {name}"
      else if pattern then
        let h <- modifyGet (fun s =>
          let h := s.patternNames.getD v 0
          (h, {s with patternNames := s.patternNames.insert v (h + 1)})
        )
        let r ← f s!"{← stringifyIdent v}{if h == 0 then "" else if h == 1 then "#" else s!"#{h - 1}"}"
        modify fun s => {s with patternNames := if h == 0 then
            s.patternNames.erase v
          else
            s.patternNames.insert v h
        }
        pure r
      else
        f (← stringifyIdent v)
    | .str v "_@" => do
      let v := s!"{v}"
      makeHygienicName v f
    | .str n _ => go n true f
    | .num n _ => go n true f

def bindStr
  {α: Type} [Inhabited α] (n: String) (e: M α): M (String × α) := do
  modify fun s => {s with bvarValues := s.bvarValues.push n }
  let v <- e
  modify fun s => {s with bvarValues := s.bvarValues.pop }
  return (n, v)

def bindIf
  {α: Type} [Inhabited α] (pattern: Bool) (n: Name) (e: M α): M (String × α) := do
  withLocalName n pattern (bindStr · e)

def bind
  {α: Type} [Inhabited α] (n: Name) (e: M α): M (String × α) :=
  -- TODO: implement proper name liveness analysis
  --bindIf false n e
  bindIf true n e
