import Lean2Agda.Data.Value
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
import Lake.Util.EStateT
import Batteries.Data.Vector.Basic
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

open System (FilePath)
open Lean (Environment Options Name KVMap mkEmptyEnvironment)
open Lake (EStateT EResult)
open Batteries (Vector)
open Std (HashMap HashSet)

structure Config extends EraseConfig where
  options: Options := {}

structure Context extends Config, EraseContext, AnnotateContext, DedupConfig, MetaMContext where
  language: Language

genSubValue (Context) (AnnotateContext) toAnnotateContext
genSubValue (Context) (MetaMContext) toMetaMContext
genSubValue (Context) (EraseContext) toEraseContext
genSubValue (Context) (DedupConfig) toDedupConfig
genSubValue (Context) (Language) language

def TranslateM.run
  (config : Config) (env : Environment) (act : [Value Context] → TranslateT IO α) : IO α := do
  let rand := (String.mk $ ← (List.replicate 16 ' ').mapM fun _ => do pure $ Char.ofNat $ ← IO.rand 33 126)
  let projectKeyword := Name.str Name.anonymous ("$$project_" ++ rand)
  let implicitKeyword := Name.str Name.anonymous ("$$implicit_" ++ rand)
  let dedupPrefix := Name.str Name.anonymous ("$$dedup_" ++ rand)
  let binderMDatas := Vector.ofFn (λ i ↦ KVMap.empty.setInt implicitKeyword i.val)
  let dummyEnv ← mkEmptyEnvironment
  let language := Agda

  have := mkValueAs Context { config with dummyEnv, projectKeyword, implicitKeyword, binderMDatas, dedupPrefix, language}
  let r ← EStateT.run ({ env } : TranslateState) do
    act

  match r with
  | .error msg _ => throw <| IO.userError (← msg.toString)
  | .ok a _ => pure a
