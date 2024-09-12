import Lean2Agda.Data.Monad

import Lean.Meta.Basic
import Lean.Util.CollectLevelParams
import Lean.AddDecl
import Std.Data.HashMap.Basic

open Lean hiding HashMap HashSet
open Std (HashMap)

local instance [Repr α]: ToFormat α where
  format := repr

variable {M : Type → Type} [Monad M] [MonadExceptOf MessageData M]

local instance [MonadStateOf α M]: MonadReaderOf α M where
  read := get

structure DedupData where
  dedupPrefix: Name

structure DedupConfig extends DedupData where
  options: Options

genSubReader (DedupConfig) (DedupData) toDedupData

structure DedupState where
  map: HashMap ExprStructEq Expr := {}
  numConsts: Nat := 0
  deriving Inhabited

structure DedupedExpr where
  deduped: Expr
  deriving Inhabited

inductive PreserveKind where
| lam
| forAllE
  deriving Repr, BEq

structure Preserve where
  kind: PreserveKind
  n: Nat

partial def dedupExprs [MonadReaderOf DedupConfig M]
    [MonadStateOf DedupState M] [MonadLiftT MetaM M]
    (es: Array (Expr × Option Preserve)): M (Array DedupedExpr) :=
  let extract {M: Type → Type} [Monad M] [MonadReaderOf DedupConfig M] [MonadStateOf DedupState M] [MonadLiftT MetaM M]
      (e: Expr) (type: Expr): M Expr := do
    let idx ← modifyGetThe DedupState (λ {map, numConsts} ↦ (numConsts, {map, numConsts := numConsts.succ}))
    let name := Name.num (← read).dedupPrefix idx
    let levelParamsState: CollectLevelParams.State := {}
    let levelParamsState := levelParamsState.collect type
    let levelParamsState := levelParamsState.collect e
    let levelParams := levelParamsState.params.data
    let defn: DefinitionVal := {
      hints := .abbrev
      safety := .safe
      name
      levelParams
      type
      value := e
    }
    let decl := .defnDecl defn
    let options := (← read).options
    let m: MetaM Unit := do
      let r ← modifyGetThe Core.State λ st ↦ match st.env.addDecl options decl with
        | .ok env => (.ok (), {st with env})
        | .error err => (.error err, st)
      ofExceptKernelException r
    m

    pure <| .const name (levelParams.map (.param ·))

  let rec mark {M: Type → Type} [Monad M] [MonadStateOf (HashMap ExprStructEq (Option Expr)) M] [MonadLiftT MetaM M]
      (e: Expr): M Unit := do
    let cont ←
      if e.hasLooseBVars || e.approxDepth == 0 then -- TODO: support extracting exprs with loose bvars
        pure true
      else
        let entry ← modifyGet (·.getThenInsertIfNew? e none)
        match entry with
        | .some entry =>
          if entry.isNone then
            let type ← Meta.inferType e
            mark type
            modify (·.insert e (some type))
          pure false
        | .none =>
          pure true
    if cont then
      match e with
      | .forallE _ d b _ => do mark d; mark b
      | .lam _ d b _ => do mark d; mark b
      | .mdata _ b => do mark b
      | .letE _ t v b _  => do mark t; mark v; mark b
      | .app f b => do mark f; mark b
      | .proj _ _ b => do mark b
      | _ => pure ()

  let rec markPreserve {M: Type → Type} [Monad M] [MonadExceptOf MessageData M] [MonadStateOf (HashMap ExprStructEq (Option Expr)) M] [MonadLiftT MetaM M]
    (e: Expr) (p: PreserveKind) (n: Nat): M Unit := do
    if n == 0 then
      mark e
    else
      let fail :=
        throw m!"expected {p} when deduping with {n} binders to preserve left"
      match e with
      | .forallE _ d b _ => do
        if p != .forAllE then
          fail
        else
          mark d; markPreserve b p (n - 1)
      | .lam _ d b _ =>
        if p != .lam then
          fail
        else
          mark d; markPreserve b p (n - 1)
      | .mdata _ b => do markPreserve b p n
      | _ =>
        fail

  let rec dedup {M: Type → Type} [Monad M] [MonadReaderOf DedupConfig M] [MonadLiftT MetaM M]
      [MonadReaderOf (HashMap ExprStructEq (Option Expr)) M] [MonadStateOf DedupState M]
      (e: Expr): M Expr := do
    let replacement := (← get).map.get? e
    if let .some replacement := replacement then do
      pure <| replacement
    else
      let e' ← match e with
      | e@(.forallE _ d b _) => pure e.updateForallE! <*> dedup d <*> dedup b
      | e@(.lam _ d b _) => pure e.updateLambdaE! <*> dedup d <*> dedup b
      | e@(.mdata _ b) => e.updateMData! <$> dedup b
      | e@(.letE _ t v b _) => pure e.updateLet! <*> dedup t <*> dedup v <*> dedup b
      | e@(.app l r) => pure e.updateApp! <*> dedup l <*> dedup r
      | e@(.proj _ _ b) => e.updateProj! <$> dedup b
      | e => pure e
      match (← read).get? e with
      | .some (.some replacementType) =>
        let replacement ← extract e' (← dedup replacementType)
        modifyGet (λ {map, numConsts} ↦ ((), {map := map.insert e replacement, numConsts}))
        pure <| replacement
      | _ =>
        pure <| e'

  let rec dedupPreserve {M: Type → Type} [Monad M] [MonadExceptOf MessageData M] [MonadReaderOf DedupConfig M] [MonadLiftT MetaM M]
      [MonadReaderOf (HashMap ExprStructEq (Option Expr)) M] [MonadStateOf DedupState M]
      (e: Expr) (p: PreserveKind) (n: Nat): M Expr := do
    if n == 0 then
      dedup e
    else
      let fail :=
        throw m!"expected {p} when deduping during replacement with {n} binders to preserve left"
      match e with
      | .forallE _ d b _ => do
        if p != .forAllE then
          fail
        else
          pure e.updateForallE! <*> dedup d <*> dedupPreserve b p (n - 1)
      | .lam _ d b _ =>
        if p != .lam then
          fail
        else
          pure e.updateLambdaE! <*> dedup d <*> dedupPreserve b p (n - 1)
      | .mdata _ b => e.updateMData! <$> dedupPreserve b p n
      | _ =>
        fail

  StateT.run' (m := M) (s := (HashMap.empty: HashMap ExprStructEq (Option Expr))) do
    es.forM λ (e, p) ↦ do
      match p with
      | .none => mark e
      | .some p => markPreserve e p.kind p.n
    es.mapM λ (e, p) ↦ do
      pure { deduped :=
        ← match p with
        | .none => dedup e
        | .some p => dedupPreserve e p.kind p.n
      }

def isDedupConst [MonadReaderOf DedupConfig M]
    (name: Name): M Bool := do
  let needed ← match name with
  | .num p _ =>
    if p == (← read).dedupPrefix then
      return true
    else
      pure false
  | _ =>
    pure false
