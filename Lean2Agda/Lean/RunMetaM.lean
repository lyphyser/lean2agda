import Lean2Agda.Data.Value
import Lean.CoreM
import Lean.Meta.Basic

open Lean (FileMap Options Environment MessageData)
open Lean.Meta (MetaM)

variable {M : Type → Type} [Monad M] [MonadExceptOf MessageData M]

structure MetaMContext where
  dummyEnv : Environment
  options: Options := {}

def runMetaM'' [Value MetaMContext] [MonadLiftT IO M]
  {α : Type} (env: Environment) (m: MetaM α): M (α × Environment) := do
  let ctx ← pure <| {
    fileName := "<internal>",
    fileMap := FileMap.ofString ""
    options := (valueOf MetaMContext).options
    --maxHeartbeats := 200000 * 1000 * 100
  }

  let s: Lean.Core.State := {env}

  let ⟨x, s⟩ ← Lean.Core.CoreM.toIO (ctx := ctx) (s := s) do
    MetaM.run' do
      m

  pure ⟨x, s.env⟩

def runMetaMMod' [Value MetaMContext] [MonadStateOf Environment M] [MonadLiftT IO M]
    {α : Type} (m: MetaM α): M α := do
  let dummyEnv := (valueOf MetaMContext).dummyEnv
  let env ← modifyGetThe Environment λ e ↦ (e, dummyEnv)

  let ⟨x, env⟩ ← runMetaM'' env m

  set env
  pure x

def runMetaMMod [Value MetaMContext] [MonadStateOf Environment M] [MonadLiftT IO M]
    (S: Type) [Inhabited S] [MonadStateOf S M]
    {α : Type} (m: (ExceptT MessageData (StateT S MetaM)) α): M α := do
  let s ← modifyGet (·, default)

  let ⟨x, s⟩ ←
    runMetaMMod' do
      StateT.run (s := s) do
        ExceptT.run
          m

  set s
  MonadExcept.ofExcept x

def runMetaMRo' [Value MetaMContext] [Value Environment] [MonadLiftT IO M]
    {α : Type} (m: MetaM α): M α := do
  let env := valueOf Environment
  let ⟨x, _⟩ ← runMetaM'' env m
  pure x

def runMetaMRo [Value MetaMContext] [Value Environment] [MonadLiftT IO M]
    (S: Type) [Inhabited S] [MonadStateOf S M]
    {α : Type} (m: (ExceptT MessageData (StateT S MetaM)) α): M α := do
  let s ← modifyGet (·, default)

  let ⟨x, s⟩ ←
    runMetaMRo' do
      StateT.run (s := s) do
        ExceptT.run
          m

  set s
  MonadExcept.ofExcept x
