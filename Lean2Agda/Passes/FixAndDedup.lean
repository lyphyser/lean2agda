import Lean2Agda.Passes.FixImplicits
import Lean2Agda.Passes.Dedup
import Lean2Agda.Lean.RunMetaM

open Lean (Environment Name Expr MessageData)

variable {M: Type → Type} [Monad M] [MonadExceptOf MessageData M]

def fixAndDedupExprsFor [MonadStateOf Environment M] [MonadStateOf DedupState M]
  [MonadReaderOf MetaMContext M] [MonadReaderOf DedupConfig M]
     [MonadLiftT IO M]
    (name: Name) (es: Array (Expr × Option Expr × Option Preserve)): M (Array DedupedExpr) := do
  if ← isDedupConst name then
    pure <| es.map ({ deduped := ·.1 })
  else
    runMetaMMod DedupConfig DedupState do
      -- TODO: pass the type to dedupExprs so we might save some type inference
      let es ← es.mapM (λ (e, ty, preserve) ↦ do pure (⟨← fixExpr e ty, preserve⟩ : (_ × _)))
      dedupExprs es
