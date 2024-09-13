import Lean2Agda.Data.Value
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

variable [Value EraseContext] [Value AnnotateContext] [Value MetaMContext] [Value Environment]

section
local macro "M": term => `(ExceptT MessageData IO)

def processExpr
    (constInstance: ConstInstance) (levelParams: Vector Name constInstance.constAnalysis.numLevels) (e : DedupedExpr) (keep: Nat): M (ProcessedExpr × AnnotationData) := do
  let e := e.deduped

  have: MonadStateOf Unit M := unitStateOf
  let (e, annotationData) ← StateT.run (s := ({} : AnnotationData)) do
    runMetaMRo AnnotationData do
      annotateExpr e

  -- this must happen last, because it can make the Expr invalid due to erasing lambda types
  let e: ProcessedExpr := {
      constInstance,
      erased := eraseUnused (valueOf EraseContext) annotationData levelParams e keep
    }
  pure (e, annotationData)
end
