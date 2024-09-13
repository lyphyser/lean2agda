import Lean2Agda.Data.Value
import Lean2Agda.Data.Monad
import Lean.CoreM
import Lean.Meta.Basic

open Lean (FileMap Options Environment MessageData)
open Lean.Meta (MetaM)
open Lake (EStateT)

structure DummyEnvironment where
  dummyEnv : Environment

structure MetaMContext extends DummyEnvironment where
  options: Options := {}

genSubValue (MetaMContext) (DummyEnvironment) toDummyEnvironment

variable [Value MetaMContext]

def runMetaM''
  {α : Type} (env: Environment) (m: MetaM α): IO (α × Environment) := do
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

def runMetaMRo' [Value Environment]
    {α : Type} (m: MetaM α): IO α := do
  let env := valueOf Environment
  let ⟨x, _⟩ ← runMetaM'' env m
  pure x

variable {M : Type → Type} [Monad M] [MonadExceptOf MessageData M]

def runMetaMMod' [Value MetaMContext] [MonadStateOf Environment M] [MonadLiftT IO M]
    {α : Type} (m: MetaM α): M α := do
  let dummyEnv := (valueOf DummyEnvironment).dummyEnv
  let env ← modifyGetThe Environment λ e ↦ (e, dummyEnv)

  let ⟨x, env⟩ ← runMetaM'' env m

  set env
  pure x

def runMetaMMod [MonadStateOf Environment M] [MonadLiftT IO M]
    (S: Type) [Inhabited S] [MonadStateOf S M]
    {α : Type} (m: (EStateT MessageData S MetaM) α): M α := do
  let s ← modifyGet (·, default)

  let r ←
    runMetaMMod' do
      EStateT.run s do
        m

  r.act

def runMetaMRo [Value Environment] [MonadLiftT IO M]
    (S: Type) [Inhabited S] [MonadStateOf S M]
    {α : Type} (m: (EStateT MessageData S MetaM) α): M α := do
  let s ← modifyGet (·, default)

  let r ←
    runMetaMRo' do
      EStateT.run s do
        m

  r.act
