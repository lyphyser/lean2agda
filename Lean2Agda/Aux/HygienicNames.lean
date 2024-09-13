import Lean2Agda.Data.Monad
import Lean2Agda.Data.Value
import Lean2Agda.Aux.Ident
import Std.Data.HashMap.Basic

open Std (HashMap)

structure HygienicNames where
  hygienicNames: HashMap String Nat := {}
  deriving Inhabited

variable [Value Language]

def makeHygienicName
  (v: String): SubState HygienicNames String :=
  let enter := λ ({hygienicNames}) ↦
      let h := hygienicNames.getD v 0
      let i := s!"{stringifyIdent v}${if h == 0 then "" else s!"{h}"}"
      ((i, h), {hygienicNames := hygienicNames.insert v (h + 1)})
  let exit := λ h ({hygienicNames}) ↦
    {hygienicNames := if h == 0 then
      hygienicNames.erase v
    else
      hygienicNames.insert v h
    }
  SubState.mk enter exit
