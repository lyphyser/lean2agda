import Lean2Agda.Aux.Ident
import Std.Data.HashMap.Basic

open Std (HashMap)

structure HygienicNames where
  hygienicNames: HashMap String Nat := {}
  deriving Inhabited

variable {M: Type → Type} [Monad M]
  [MonadStateOf HygienicNames M] [MonadReaderOf Language M]

def makeHygienicName
  (v: String) (f: String → M α): M α := do
  let h <- modifyGet (fun s =>
    let h := s.hygienicNames.getD v 0
    (h, {s with hygienicNames := s.hygienicNames.insert v (h + 1)})
  )
  let r <- f s!"{← stringifyIdent v}${if h == 0 then "" else s!"{h}"}"
  modify fun s => {s with hygienicNames := if h == 0 then
      s.hygienicNames.erase v
    else
      s.hygienicNames.insert v h
  }
  pure r
