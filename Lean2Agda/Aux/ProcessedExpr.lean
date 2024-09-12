import Lean2Agda.Data.ExtraBatteries
import Lean2Agda.Aux.ConstInstance
import Lean2Agda.Aux.BoundLevels
import Lean2Agda.Aux.ExprState
import Lean2Agda.Passes.EraseUnused
import Lean2Agda.Passes.Dedup
import Lean2Agda.Lean.RunMetaM

import Batteries.Data.Vector.Basic

open Batteries (Vector)
open Lean (Name Environment MessageData)

structure ProcessedExpr where
  constInstance: ConstInstance
  erased: ErasedExpr constInstance.constAnalysis.numLevels
  deriving Inhabited
  --levelKinds: Array LevelKind := {}

namespace ProcessedExpr
abbrev numLevels (e: ProcessedExpr) := e.constInstance.constAnalysis.numLevels
end ProcessedExpr

variable {M: Type → Type} [Monad M] [MonadExceptOf MessageData M]
  [MonadReaderOf EraseContext M] [MonadReaderOf AnnotateContext M] [MonadReaderOf MetaMContext M] [MonadReaderOf Environment M]

def bindLevelParamsWith [MonadLiftT IO M]
  {α: Type} (ci: ConstInstance) (levelParamValues: Vector Name ci.numLevels) (m: ReaderT BoundLevels M α): M α := do

  let h: levelParamValues.toArray.size = ci.constAnalysis.numLevels := by
    exact levelParamValues.size_eq
  let input2idx := h ▸ reverseHashMap levelParamValues.toArray id id

  let r: BoundLevels := {constInstance := ci, input2idx}
  --traceComment s!"BoundLevels: {repr r}"
  ReaderT.run (r := r) do
    m

def processExprAnd [MonadStateOf Environment M] [MonadLiftT IO M]
    (constInstance: ConstInstance) (levelParams: Vector Name constInstance.constAnalysis.numLevels) (e : DedupedExpr) (keep: Nat) (f: ProcessedExpr → ReaderT BoundLevels (ReaderT AnnotationData (StateT ExprState M)) α): M α := do
  let e := e.deduped

  have: MonadStateOf Unit M := unitStateOf
  let (e, annotationData) <- runMetaMRo AnnotateContext Unit do
    StateT.run (s := ({} : AnnotationData)) do
      annotateExpr (ε := MessageData) e

  -- this must happen last, because it can make the Expr invalid due to erasing lambda types
  let e: ProcessedExpr := {
      constInstance,
      erased := eraseUnused (← readThe EraseContext) annotationData levelParams e keep
    }
  StateT.run' (s := ({} : ExprState)) do
    ReaderT.run (r := annotationData) do
      bindLevelParamsWith e.constInstance e.erased.levelParams do
        f e
