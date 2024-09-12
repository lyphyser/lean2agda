import Lean2Agda.Data.Monad
import Lean2Agda.Data.String
import Lean2Agda.Output.PFormat
import Lean2Agda.Analysis.ConstAnalysis
import Lean2Agda.Passes.Annotate
import Lean2Agda.Aux.ExprState
import Lean2Agda.Aux.Ident
import Lean2Agda.Aux.BoundLevels
import Lean2Agda.Aux.Dependencies
import Lean2Agda.Aux.GlobalNames
import Lean2Agda.Aux.ProcessedExpr
import Lean2Agda.Lean.RunMetaM
import Lean.Message

open Lean (Expr MData Level MessageData Name Environment BinderInfo)
open Lean.Meta (MetaM)


variable {M: Type → Type} [Monad M] [MonadExceptOf MessageData M]
  [MonadLiftT IO M] [MonadStateOf GlobalAnalysis M] [MonadStateOf GlobalNames M] [MonadStateOf Dependencies M] [MonadStateOf ExprState M]
  [MonadReaderOf BoundLevels M] [MonadReaderOf AnnotationData M] [MonadReaderOf Environment M]
  [MonadReaderOf DedupData M] [MonadReaderOf Language M] [MonadReaderOf MetaMContext M] [MonadReaderOf AnnotateContext M]

local instance : Coe α (M α) where
  coe := pure

abbrev FormatT (M: Type → Type) [Monad M] := ExceptT MessageData <|
  ReaderT BoundLevels <| ReaderT DedupData <| ReaderT Language <| ReaderT AnnotationData <| ReaderT Environment <| ReaderT AnnotateContext <| ReaderT MetaMContext <|
  StateT GlobalAnalysis <| StateT GlobalNames <| StateT Dependencies <| StateT ExprState <| M

def formatLevel
  (ci: ConstInstance) (nl : NormLevel ci.numLevels): M PFormat := do
  let {add, max := {const, params}} := nl

  if params.toArray.all (·.isNone) then
    lconst (add + const)
  else
    let es := if const != 0 then
      #[lconst const]
    else
      #[]
    let es ← pure <| es.append <| ← Fin.foldlM ci.numLevels (init := #[]) λ ps l => do
      match params[l] with
      | .none =>
        ps
      | .some padd =>
        ps.push <| ← do match ci.idx2output[l] with
        | .none => lconst <| (panic! "zero level param in normalized level!") + padd
        | .some n => pure <| ladd padd <| ← lparam n

    ladd add (lmax es.toList)
where
  lparam: Name → M PFormat
  | .anonymous => pure $ token $ "_"
  | .str Name.anonymous v => do pure $ token $ ← stringifyIdent v
  | n => throw m!"unexpected level name: {n}"

def formatConst (n: Name) (us: Array Level) (f: String → String) (withLevels: Bool): M PFormat := do
  let constAnalysis ← getOrComputeConstAnalysis n
  let boundLevels ← readThe BoundLevels
  let ucs ← us.mapM (resolveLevel boundLevels)
  let ucs ← toVector ucs constAnalysis.numLevels "levels in const usage expression"
  let ccs := constAnalysis.levelClauses.map (OrClause.subst · (ucs.map (·.toClause)))
  let levelInstance ← ccs.mapM (resolveSimplifiedLevelClause boundLevels.constInstance)
  let ucs := specializeLevelParams constAnalysis levelInstance ucs

  addDependency n levelInstance.toArray

  let c := token (f (← stringifyGlobalName n levelInstance))

  if withLevels && !us.isEmpty then
    let levels: List PFormat := (← ucs.mapM <| fun nl => do pure <| encloseWith levelBinderSeps (← formatLevel boundLevels.constInstance nl)).toList
    pure <| app c levels
  else
    c

def formatExprInner
  (mdatas: List MData) (e : Expr) : M PFormat := do
  try
    pure <| ← goWithMData mdatas e
  catch err =>
    throw m!"in expression {e}\n{err}"
where
  go (e : Expr) := goWithMData [] e

  argName: Expr → Nat → M Name
  | .forallE n _ _ _, .zero => n
  | .forallE _ _ b _, .succ n => argName b n
  | .mdata _ e, n => argName e n
  | _, _ => throw m!"argument not found!"

  proj (mdatas: List MData) (typeName: Name) (idx: Nat): M PFormat := do
    let projectKeyword := (← read).projectKeyword
    let projId: Option Nat := mdatas.findSome? (·.get? projectKeyword)
    let .some projId := projId | throw m!"proj without our metadata: {e} {mdatas}"
    let projectionLevels: List Level := (← readThe AnnotationData).projectionLevels[projId]!

    let env := ← readThe Environment
    let induct := env.find? typeName |>.get!
    let .inductInfo induct := induct | throw m!"projection type is not an inductive"
    let [ctor] := induct.ctors | throw m!"projection type is not an 1-ctor inductive"

    let .ctorInfo ctor := (env.find? ctor |>.get!) | throw m!"inductive ctor is not a ctor"
    let fieldName := ← argName ctor.type (ctor.numParams + idx)
    let .str Name.anonymous fieldName := fieldName | throw m!"unexpected field name"

    let fieldName ← stringifyIdent fieldName
    formatConst typeName projectionLevels.toArray (· ++ "." ++ fieldName) true

  handleAppArg (mdatas: List MData) (e: Expr): M PFormat := do
    let e <- go e
    let implicitKeyword := (← readThe AnnotateContext).implicitKeyword
    pure $ encloseWith (maybeBinderSeps <| optionIntToBinder <| mdatas.findSome? (·.get? implicitKeyword)) e

  goApp (mdatas: List MData) (f: Expr) (es: List PFormat) : M PFormat := do
    match f with
    | .app f e =>
      goApp [] f ((← handleAppArg mdatas e) :: es)
    | .proj typeName idx e =>
      let e <- go e
      app (← proj mdatas typeName idx) (e :: es)
    | .const n us =>
      app (← formatConst n us.toArray id true) es
    | .mdata m f =>
      goApp (m :: mdatas) f es
    | f =>
      app (← go f) es

  goWithMData (mdatas: List MData) (e : Expr): M PFormat := do
    match e with
    | .bvar i =>
      let a := (← get).bvarValues
      let i := a.size - 1 - i
      let v := a[i]!
      token v
    | .sort l =>
      let boundLevels ← readThe BoundLevels
      let {add, max := {const, params}} := ← resolveLevel boundLevels l
      if params.toArray.all (·.isNone) then
        match add with
        | 0 => token "Prop"
        | 1 => token "Set₁"
        | 2 => token "Set₂"
        | 3 => token "Set₃"
        | 4 => token "Set₄"
        | 5 => token "Set₅"
        | 6 => token "Set₆"
        | 7 => token "Set₇"
        | 8 => token "Set₈"
        | 9 => token "Set₉"
        | .succ n => app (token "Type") [lconst n]
      else
        match add with
        | .succ addp =>
          app (token "Type") [← formatLevel boundLevels.constInstance {add := addp, max := {const, params}}]
        | .zero =>
          app (token "Set") [← formatLevel boundLevels.constInstance {add, max := {const, params}}]
    | .const n us =>
      formatConst n us.toArray id true
    | .app f e =>
      goApp [] f [← handleAppArg mdatas e]
    | .lam n d b bi =>
      let (n, b) <- bind n (go b)
      if d == .const Name.anonymous [] then
        lambdaArrow [encloseWith (maybeBinderSeps bi) (token n)] b
      else
        -- TODO: this should probably be maybeBinderSeps, and also should fix the lambda representation
        lambdaArrow [encloseWith (alwaysBinderSeps bi) (typing (token n) (← go d))] b
    | .letE n d v b _ =>
      let (n, b) <- bind n (go b)
      inExpr [stmts [typing (kwToken "let" n) (← go d), define (token n) [← go v]]] b
    | .forallE n d b bi =>
      let (n, b) <- bind n (go b)
      let d ← go d
      let a: PFormat <- if n == "_" then
        encloseWith (maybeBinderSeps bi) d
      else
        encloseWith (alwaysBinderSeps bi) (typing (token n) d)
      arrow [a] b
    | .fvar .. => throw m!"fvar"
    | .mvar .. => throw m!"mvar"
    | .proj t i e =>
      app (← proj mdatas t i) [← go e]
    | .lit (.natVal i) => token s!"{i}"
    | .lit (.strVal s) => token s!"\"{s.escape}\""
    | .mdata m e => goWithMData (m :: mdatas) e

def extractLevelParams
  (levelParams: List Name) (n: Nat): M ((Array ((Option BinderInfo) × String × PFormat)) × List Name) := do
  let (a, b) <- go levelParams n
  pure (a.reverse, b)
where
  go (levelParams: List Name) (num: Nat): M ((Array ((Option BinderInfo) × String × PFormat)) × List Name) :=
    match num with
    | .zero => do pure (Array.empty, levelParams)
    | .succ num => match levelParams with
      | n :: levelParams => do
        let (n, (a, b)) <- bind n (go levelParams num)
        pure (a.push (none, n, token "Level"), b)
      | [] => throw m!"not enough level parameters"

def formatArgs (a: Array ((Option BinderInfo) × String)): List PFormat :=
  -- TODO: use a single {} for multiple consecutive arguments
  a.data.map fun (bi, s) => encloseWith (maybeLotBinderSeps bi) (token s)

def formatParams (a: Array ((Option BinderInfo) × String × PFormat)): Array PFormat :=
  -- TODO: use a single {}/() for multiple consecutive arguments of the same type
  a.map fun (bi, s, t) => encloseWith (alwaysLotBinderSeps bi) (typing (token s) t)

def formatLevelParams
  (l: List Name) : M (Array PFormat) := do
  let (params, _) ← extractLevelParams l l.length
  pure $ formatParams params

def formatExprInnerWithLevelParams
  (levelParams: List Name) (ms: List MData) (e : Expr) : M PFormat := do
  arrow (← formatLevelParams levelParams).data (← formatExprInner ms e)

def formatTypeParamsAndHandleExpr
  [Inhabited α] (e: Expr) (minimum: Nat) (strict: Bool) (f: List MData → Expr → M α): M ((Array ((Option BinderInfo) × String × PFormat)) × α) := do
  let (revTypeParams, expr) <- go [] e minimum
  pure (revTypeParams.reverse, expr)
where
  go (ms: List MData) (e: Expr) (num: Nat): M ((Array ((Option BinderInfo) × String × PFormat)) × α) :=
    match num with
    | .zero => do pure (Array.empty, ← f ms e)
    | .succ num => match e with
      | .forallE n d b bi => do
        let (n, (a, e)) <- bind n (go [] b num)
        pure (a.push (some bi, n, ← formatExprInner [] d), e)
      | .mdata m b => go (m :: ms) b (.succ num)
      | _ => do
        if strict then
          throw m!"not enough type parameters in format: {num.succ} still needed of {minimum}: at {e}"
        pure (Array.empty, ← f ms e)

def formatParamsAndHandleExpr
    [Inhabited α] (e: ProcessedExpr) (n: Nat) (strict: Bool) (f: List Name → List MData → Expr → M α): M ((Array ((Option BinderInfo) × String × PFormat)) × α) := do
  if n < e.numLevels then
    throw m!"{"" ++ panic! s!"partial extraction of level params: {n} < {e.numLevels}!!!"} partial extraction of level params: {n} < {e.numLevels}!!!"

    let (extractedLevelParams, levelParams) <- extractLevelParams e.erased.levelParams.toList n
    pure (extractedLevelParams, ← f levelParams [] e.erased.expr)
  else
    let levelParams := specializeLevelParams e.constInstance.constAnalysis e.constInstance.levelInstance e.erased.levelParams
    let (extractedLevelParams, _) <- extractLevelParams levelParams.toList levelParams.size
    let (typeParams, expr) ← formatTypeParamsAndHandleExpr e.erased.expr (n - e.erased.levelParams.size) strict (f [])
    pure (extractedLevelParams ++ typeParams, expr)

def formatParamsAndProcessedExpr
    (e: ProcessedExpr) (n: Nat): M ((Array ((Option BinderInfo) × String × PFormat)) × PFormat) :=
  formatParamsAndHandleExpr e n true (formatExprInnerWithLevelParams · · ·)

def formatArgsAndHandleExpr
    (e: ProcessedExpr) (f: List MData → Expr → Nat → M ((Array ((Option BinderInfo) × String)) × PFormat)): M ((Array ((Option BinderInfo) × String)) × PFormat) := do
  let levelParams := specializeLevelParams e.constInstance.constAnalysis e.constInstance.levelInstance e.erased.levelParams
  let (a, b) <- goLevels levelParams.toList e.erased.expr
  pure (a.reverse, b)
where
  goLevels (levels: List Name) (e: Expr) : M ((Array ((Option BinderInfo) × String)) × PFormat) :=
    match levels with
    | n :: levels => do
      let (n, (a, b)) <- bindIf true n (goLevels levels e)
      pure (a.push (none, n), b)
    | [] => goExpr [] e 0

  goExpr (mdatas: List MData) (e: Expr) (depth: Nat): M ((Array ((Option BinderInfo) × String)) × PFormat) := do
    match e with
    | .mdata m b => goExpr (m :: mdatas) b depth
    | .lam n _d b bi =>
      let (n, (a, b)) <- bindIf true n (goExpr [] b (depth + 1))
      pure (a.push (bi, n), b)
    | e => do
      let (a, v) ← f mdatas e depth
      (a.reverse, v)

def runFormatTMetaM [MonadLiftT IO M]
  {α : Type} (m: (FormatT MetaM) α): M α := do
  let boundLevels <- readThe BoundLevels
  let dedupData <- readThe DedupData
  let language <- readThe Language
  let annotationData <- readThe AnnotationData
  let environment ← readThe Environment
  let annotateContext ← readThe AnnotateContext
  let metaMContext ← readThe MetaMContext

  let globalAnalysis ← modifyGetThe GlobalAnalysis (·, default)
  let globalNames ← modifyGetThe GlobalNames (·, default)
  let dependencies ← modifyGetThe Dependencies (·, default)
  let exprState ← modifyGetThe ExprState (·, default)

  let ⟨((((x, globalAnalysis), globalNames), dependencies), exprState), _environment⟩ ←
    runMetaM'' environment do
      StateT.run (s := exprState) do
      StateT.run (s := dependencies) do
      StateT.run (s := globalNames) do
      StateT.run (s := globalAnalysis) do
      ReaderT.run (r := metaMContext) do
      ReaderT.run (r := annotateContext) do
      ReaderT.run (r := environment) do
      ReaderT.run (r := annotationData) do
      ReaderT.run (r := language) do
      ReaderT.run (r := dedupData) do
      ReaderT.run (r := boundLevels) do
      ExceptT.run
        m

  set exprState
  set dependencies
  set globalNames
  set globalAnalysis
  MonadExcept.ofExcept x

partial def formatEagerImplicitsAndHandleExpr [MonadLiftT IO M] {α} [Inhabited α] (e: Expr) (skip: Nat)
    (f: List MData → Expr → (FormatT MetaM) ((Array ((Option BinderInfo) × String)) × α))
    : M (Array ((Option BinderInfo) × String) × α) := do
  let (revTypeParams, expr) <-
    runFormatTMetaM do
      go [] e skip #[]
  pure (revTypeParams.reverse, expr)
where
  go (ms: List MData) (e: Expr) (num: Nat) (fvars: Array Expr): (FormatT MetaM) ((Array ((Option BinderInfo) × String)) × α) := do
    let ⟨e, fvars⟩ ←
      match e with
      | e@(.forallE ..) => pure (⟨e, fvars⟩ : (_ × _))
      | e => pure ⟨← Lean.Meta.whnf (e.instantiateRev fvars), #[]⟩
    match e with
    | .forallE n d b bi => do
      Lean.Meta.withLocalDecl n bi (d.instantiateRev fvars) fun fv => do
        let fvars := fvars.push fv
        match num with
        | .succ num =>
          go [] b num fvars
        | .zero =>
          if bi != default then
            let n := if n == Name.anonymous then
              `l
            else
              n
            let (n, (a, e)) <- bind n (go [] b 0 fvars)
            pure (a.push (some bi, n), e)
          else
            let (a, v) ← f ms e
            pure (a.reverse, v)
    | .mdata m b => go (m :: ms) b num fvars
    | _ => do
      if num != 0 then
        have: MonadExceptOf MessageData (FormatT MetaM) := instMonadExceptOfExceptTOfMonad _ _
        throw m!"not enough type parameters when handling eager implicits: {num.succ} still needed of {skip}: at {e}"
      f ms e

def formatArgsWithEagerImplicits [MonadLiftT IO M]
    (ty: DedupedExpr) (f: Nat → Nat) (e: ProcessedExpr) : M ((Array ((Option BinderInfo) × String)) × PFormat) := do
  formatArgsAndHandleExpr e λ ms e d ↦ do
    let (a, e) ← formatEagerImplicitsAndHandleExpr ty.deduped (f d) λ _ _ ↦ do
      pure (Array.empty, ← formatExprInner ms e)
    (a, app e (a.toList.map (λ (bi, s) ↦ encloseWith (maybeLotBinderSeps bi) (token s))))

def substTypeParams
    [Inhabited α] (mdatas: List MData) (e : Expr) (typeValues: Array String) (f: List MData → Expr → M α): M α := do
  go mdatas e typeValues.size
where
  go (mdatas: List MData) (e: Expr) (num: Nat): M α :=
    match num with
    | .zero => f mdatas e
    | .succ num => match e with
      | .forallE _ _ b _ => do
        let (_, e) <- bindStr (typeValues.get! (typeValues.size - num.succ)) (go [] b num)
        pure e
      | .mdata m b => go (m :: mdatas) b (.succ num)
      | _ => throw m!"not enough type parameters in subst: {num.succ} still needed of {typeValues.size} for {typeValues}: at {e}"
