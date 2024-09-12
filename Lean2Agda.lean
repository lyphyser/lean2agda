import Lean2Agda.Data.Monad
import Lean2Agda.Data.ExtraBatteries
import Lean2Agda.Data.OrClause
import Lean2Agda.Data.MaxLevel
import Lean2Agda.Analysis.ConstAnalysis
import Lean2Agda.Passes.Dedup
import Lean2Agda.Passes.FixImplicits
import Lean2Agda.Passes.EraseUnused
import Lean2Agda.Passes.Annotate
import Lean2Agda.Output.Pretty
import Lean2Agda.Output.PFormat
import Lean2Agda.Output.Language
import Lean2Agda.Output.Language.Agda
import Lean2Agda.Aux.GlobalNames
import Lean2Agda.Aux.ModulesState
import Lean2Agda.Main.Translate
import Lean2Agda.Lean.RunMetaM

import Lean
import Lean.CoreM
import Lean.Meta.Basic
import Lean.Meta.InferType
import Batteries.Data.Vector.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

open System (FilePath)
open Lean hiding HashMap HashSet
open Batteries (Vector)
open Std (HashMap HashSet)

variable {M : Type → Type} [Monad M] [MonadExceptOf MessageData M]

structure Config extends EraseConfig where
  options: Options := {}

structure Context extends Config, EraseContext, AnnotateContext, DedupConfig, MetaMContext where
  language: Language

genSubReader (Context) (AnnotateContext) toAnnotateContext
genSubReader (Context) (MetaMContext) toMetaMContext
genSubReader (Context) (EraseContext) toEraseContext
genSubReader (Context) (DedupConfig) toDedupConfig
genSubReader (Context) (Language) language

structure State where
  env : Environment
  modulesState : ModulesState := default
  dedupState : DedupState := {}
  globalNames : GlobalNames := {}
  globalAnalysis: GlobalAnalysis := {}
  visited: Visited := {}

genSubMonad (State) (GlobalAnalysis) globalAnalysis globalAnalysis
genSubMonad (State) (GlobalNames) globalNames globalNames
genSubMonad (State) (DedupState) dedupState dedupState
genSubMonad (State) (Visited) visited visited
genSubMonad (State) (ModulesState) modulesState modulesState

instance [base: MonadStateOf State M] [MonadReaderOf Context M]: MonadStateOf Environment M where
    get := do pure (← base.get).env
    modifyGet f := do
      let dummy := (← read).dummyEnv
      pure (← base.modifyGet (λ σ ↦
        let v := σ.env
        let σ := {σ with env := dummy}
        let (r, σ') := f v
        (r, {σ with env := σ'})
      ))
    set σ' := base.modifyGet (λ σ ↦ ((), {σ with env := σ'}))

abbrev OurT.{v} (m: Type → Type v): Type → Type v :=
  (ExceptT MessageData (ReaderT _root_.Context (StateT _root_.State m)))

abbrev OurM := OurT IO

def M.run
  (config : Config) (env : Environment) (act : OurM α) : IO α := do
  let rand := (String.mk $ ← (List.replicate 16 ' ').mapM fun _ => do pure $ Char.ofNat $ ← IO.rand 33 126)
  let projectKeyword := Name.str Name.anonymous ("$$project_" ++ rand)
  let implicitKeyword := Name.str Name.anonymous ("$$implicit_" ++ rand)
  let dedupPrefix := Name.str Name.anonymous ("$$dedup_" ++ rand)
  let binderMDatas := Vector.ofFn (λ i: Fin 4 ↦ KVMap.empty.setInt implicitKeyword i)
  let dummyEnv ← mkEmptyEnvironment
  let language := Agda

  let r ← StateT.run' (s := ({ env } : _root_.State)) do
    ReaderT.run (r := { config with dummyEnv, projectKeyword, implicitKeyword, binderMDatas, dedupPrefix, language}) do
      ExceptT.run do
        act

  match r with
  | Except.error msg => throw <| IO.userError (← msg.toString)
  | Except.ok a => pure a
