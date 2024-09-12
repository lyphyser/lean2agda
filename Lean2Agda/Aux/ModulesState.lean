import Lean2Agda.Aux.ModuleState

import Lean.Environment

open System (FilePath)
open Lean (Name ModuleIdx)

deriving instance Hashable, Repr for ModuleIdx

def appendSuffixDirToPath (path: FilePath) (name: Name): FilePath :=
  match name with
  | .anonymous => path
  | .str _ s => path / s
  | .num _ n => path / (toString n)

def appendSuffixFNameToPath (path: FilePath) (name: Name): FilePath :=
  let ext := ".agda"
  match name with
  | .anonymous => path
  | .str _ s => path / (s ++ ext)
  | .num _ n => path / ((toString n) ++ ext)

mutual
  def appendPrefixToPath (path: FilePath) (name: Name): FilePath :=
    match name with
    | .anonymous => path
    | .str p _ => appendToPath path p
    | .num p _ => appendToPath path p

  def appendToPath (path: FilePath) (name: Name): FilePath :=
    appendSuffixDirToPath (appendPrefixToPath path name) name
end

def ModulesState := Option ModuleState
  deriving Inhabited

variable {M: Type → Type} [Monad M] [MonadLiftT IO M]

def getOrOpenOutputModuleForConst [MonadStateOf ModulesState M]
  (_ci: ConstAnalysis): M ModuleState := do
  match ← getThe ModulesState with
  | .some ms => pure ms
  | .none =>
    let output ← (IO.getStdout : IO _)
    let ms: ModuleState := {output}
    ReaderT.run (r := ms) do
      outputModulePrelude

    let mses: ModulesState := (some ms : ModulesState)
    set mses
    pure ms
