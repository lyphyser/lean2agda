import Lean2Agda.Data.Value
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
import Lake.Util.EStateT

open Lean (Expr MData Level MessageData Name Environment BinderInfo)
open Lake (EStateT)
open Lean.Meta (MetaM)

structure FormatState where
  globalNames : GlobalNames
  globalAnalysis: GlobalAnalysis
  dependencies: Dependencies
  exprState: ExprState
  deriving Inhabited

genSubMonad (FormatState) (GlobalAnalysis) globalAnalysis globalAnalysis
genSubMonad (FormatState) (GlobalNames) globalNames globalNames
genSubMonad (FormatState) (ExprState) exprState exprState
genSubMonad (FormatState) (Dependencies) dependencies dependencies

abbrev FormatT (M: Type → Type) [Monad M] := EStateT MessageData FormatState <| M

-- TODO: maybe we should autogenerate this by changing genSubMonad, and possibly implement MonadStateOf instead of only MonadLift
instance {M: Type → Type} [Monad M] [MonadExceptOf MessageData M] {N: Type → Type} [Monad N] [MonadLiftT N M]
  [MonadStateOf GlobalNames M] [MonadStateOf GlobalAnalysis M] [MonadStateOf Dependencies M] [MonadStateOf ExprState M]:
  MonadLiftT (FormatT N) M where
  monadLift act := do
    let s := {
      globalNames := ← modifyGetThe GlobalNames (·, default)
      globalAnalysis := ← modifyGetThe GlobalAnalysis (·, default)
      dependencies := ← modifyGetThe Dependencies (·, default)
      exprState := ← modifyGetThe ExprState (·, default)
    }
    let r :=  EStateT.run s act
    let r ← liftM r
    let s := r.state
    set s.globalNames
    set s.globalAnalysis
    set s.dependencies
    set s.exprState
    match r with
    | .ok x _ => pure x
    | .error e _ => throw e

variable [Value BoundLevels] [Value AnnotationData] [Value Environment]
  [Value DedupData] [Value Language] [Value MetaMContext] [Value AnnotateContext]

local macro "M": term => `(FormatT IO)

def bindStr
  {α: Type} [Inhabited α] (n: String) (e: M α): M (String × α) := do
  (bindStr' n).withMe λ n ↦ do pure (n, ← e)

def bindIf
  {α: Type} [Inhabited α] (pattern: Bool) (n: Name) (e: M α): M (String × α) := do
  (← bindIf' pattern n).withMe λ n ↦ do pure (n, ← e)

def bind {α: Type} [Inhabited α] (n: Name) (e: M α): M (String × α) := do
  (← bind' n).withMe λ n ↦ do pure (n, ← e)

def bindMM {α: Type} [Inhabited α] (n: Name) (e: (FormatT MetaM) α): (FormatT MetaM) (String × α) := do
  (← bind' n).withMe λ n ↦ do pure (n, ← e)

def formatLevel
  (ci: ConstInstance) (nl : NormLevel ci.numLevels): M PFormat := do
  let {add, max := {const, params}} := nl

  if params.toArray.all (·.isNone) then
    pure <| lconst (add + const)
  else
    let es := if const != 0 then
      #[lconst const]
    else
      #[]
    let es ← pure <| es.append <| ← Fin.foldlM ci.numLevels (init := #[]) λ ps l => do
      match params[l] with
      | .none =>
        pure <| ps
      | .some padd =>
        pure <| ps.push <| ← do match ci.idx2output[l] with
        | .none => pure <| lconst <| (panic! "zero level param in normalized level!") + padd
        | .some n => pure <| ladd padd <| ← lparam n

    pure <| ladd add (lmax es.toList)
where
  lparam: Name → M PFormat
  | .anonymous => pure $ token $ "_"
  | .str Name.anonymous v => do pure $ token $ stringifyIdent v
  | n => throw m!"unexpected level name: {n}"

--set_option trace.Meta.synthInstance true
--set_option trace.Meta.isDefEq true

def formatConst (n: Name) (us: Array Level) (f: String → String) (withLevels: Bool): M PFormat := do
  let constAnalysis ← getOrComputeConstAnalysis n
  let boundLevels := valueOf BoundLevels
  let ucs := us.mapM (resolveLevel boundLevels)
  let ucs ← ucs
  let ucs ← toVector ucs constAnalysis.numLevels "levels in const usage expression"
  let ccs := constAnalysis.levelClauses.map (OrClause.subst · (ucs.map (·.toClause)))
  let levelInstance := ccs.mapM (resolveSimplifiedLevelClause boundLevels.constInstance)
  let levelInstance ← levelInstance
  let ucs := specializeLevelParams constAnalysis levelInstance ucs

  addDependency n levelInstance.toArray

  let c := token (f (← stringifyGlobalName n levelInstance))

  if withLevels && !us.isEmpty then
    let levels: List PFormat := (← ucs.mapM <| fun nl => do pure <| encloseWith levelBinderSeps (← formatLevel boundLevels.constInstance nl)).toList
    pure <| app c levels
  else
    pure c

def formatExprInner
  (mdatas: List MData) (e : Expr) : M PFormat := do
  try
    pure <| ← goWithMData mdatas e
  catch err =>
    throw m!"in expression {e}\n{err}"
where
  go (e : Expr) := goWithMData [] e

  argName: Expr → Nat → M Name
  | .forallE n _ _ _, .zero => pure n
  | .forallE _ _ b _, .succ n => argName b n
  | .mdata _ e, n => argName e n
  | _, _ => throw m!"argument not found!"

  proj (mdatas: List MData) (typeName: Name) (idx: Nat): M PFormat := do
    let projectKeyword := (valueOf AnnotateContext).projectKeyword
    let projId: Option Nat := mdatas.findSome? (·.get? projectKeyword)
    let .some projId := projId | throw m!"proj without our metadata: {e} {mdatas}"
    let projectionLevels: List Level := (valueOf AnnotationData).projectionLevels[projId]!

    let env := valueOf Environment
    let induct := env.find? typeName |>.get!
    let .inductInfo induct := induct | throw m!"projection type is not an inductive"
    let [ctor] := induct.ctors | throw m!"projection type is not an 1-ctor inductive"

    let .ctorInfo ctor := (env.find? ctor |>.get!) | throw m!"inductive ctor is not a ctor"
    let fieldName := ← argName ctor.type (ctor.numParams + idx)
    let .str Name.anonymous fieldName := fieldName | throw m!"unexpected field name"

    let fieldName := stringifyIdent fieldName
    formatConst typeName projectionLevels.toArray (· ++ "." ++ fieldName) true

  handleAppArg (mdatas: List MData) (e: Expr): M PFormat := do
    let e <- go e
    let implicitKeyword := (valueOf AnnotateContext).implicitKeyword
    pure $ encloseWith (maybeBinderSeps <| optionIntToBinder <| mdatas.findSome? (·.get? implicitKeyword)) e

  goApp (mdatas: List MData) (f: Expr) (es: List PFormat) : M PFormat := do
    match f with
    | .app f e =>
      goApp [] f ((← handleAppArg mdatas e) :: es)
    | .proj typeName idx e =>
      let e <- go e
      pure <| app (← proj mdatas typeName idx) (e :: es)
    | .const n us =>
      pure <| app (← formatConst n us.toArray id true) es
    | .mdata m f =>
      goApp (m :: mdatas) f es
    | f =>
      pure <| app (← go f) es

  goWithMData (mdatas: List MData) (e : Expr): M PFormat := do
    match e with
    | .bvar i =>
      let a := (← getThe ExprState).bvarValues
      let i := a.size - 1 - i
      let v := a[i]!
      pure <| token v
    | .sort l =>
      let boundLevels := valueOf BoundLevels
      let {add, max := {const, params}} := ← resolveLevel boundLevels l
      if params.toArray.all (·.isNone) then
        pure <| match add with
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
          pure <| app (token "Type") [← formatLevel boundLevels.constInstance {add := addp, max := {const, params}}]
        | .zero =>
          pure <| app (token "Set") [← formatLevel boundLevels.constInstance {add, max := {const, params}}]
    | .const n us =>
      formatConst n us.toArray id true
    | .app f e =>
      goApp [] f [← handleAppArg mdatas e]
    | .lam n d b bi =>
      let (n, b) <- bind n (go b)
      if d == .const Name.anonymous [] then
        pure <| lambdaArrow [encloseWith (maybeBinderSeps bi) (token n)] b
      else
        -- TODO: this should probably be maybeBinderSeps, and also should fix the lambda representation
        pure <| lambdaArrow [encloseWith (alwaysBinderSeps bi) (typing (token n) (← go d))] b
    | .letE n d v b _ =>
      let (n, b) <- bind n (go b)
      pure <| inExpr [stmts [typing (kwToken "let" n) (← go d), define (token n) [← go v]]] b
    | .forallE n d b bi =>
      let (n, b) <- bind n (go b)
      let d ← go d
      let a: PFormat <- if n == "_" then
        pure <| encloseWith (maybeBinderSeps bi) d
      else
        pure <| encloseWith (alwaysBinderSeps bi) (typing (token n) d)
      pure <| arrow [a] b
    | .fvar .. => throw m!"fvar"
    | .mvar .. => throw m!"mvar"
    | .proj t i e =>
      pure <| app (← proj mdatas t i) [← go e]
    | .lit (.natVal i) => pure <| token s!"{i}"
    | .lit (.strVal s) => pure <| token s!"\"{s.escape}\""
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
  pure <| arrow (← formatLevelParams levelParams).data (← formatExprInner ms e)

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
      pure <| (a.reverse, v)

partial def formatEagerImplicitsAndHandleExpr {α} [Inhabited α] (e: Expr) (skip: Nat)
    (f: List MData → Expr → (FormatT MetaM) ((Array ((Option BinderInfo) × String)) × α))
    : M (Array ((Option BinderInfo) × String) × α) := do
  let (revTypeParams, expr) <-
    runMetaMRo FormatState do
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
            let (n, (a, e)) <- bindMM n (go [] b 0 fvars)
            pure (a.push (some bi, n), e)
          else
            let (a, v) ← f ms e
            pure (a.reverse, v)
    | .mdata m b => go (m :: ms) b num fvars
    | _ => do
      if num != 0 then
        throw m!"not enough type parameters when handling eager implicits: {num.succ} still needed of {skip}: at {e}"
      f ms e

def formatArgsWithEagerImplicits
    (ty: DedupedExpr) (f: Nat → Nat) (e: ProcessedExpr) : M ((Array ((Option BinderInfo) × String)) × PFormat) := do
  formatArgsAndHandleExpr e λ ms e d ↦ do
    let (a, e) ← formatEagerImplicitsAndHandleExpr ty.deduped (f d) λ _ _ ↦ do
      pure (Array.empty, ← formatExprInner ms e)
    pure <| (a, app e (a.toList.map (λ (bi, s) ↦ encloseWith (maybeLotBinderSeps bi) (token s))))

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
