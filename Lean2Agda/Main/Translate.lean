import Lean2Agda.Data.Value
import Lean2Agda.Data.Monad
import Lean2Agda.Analysis.ConstAnalysis
import Lean2Agda.Aux.ConstInstance
import Lean2Agda.Aux.ModulesState
import Lean2Agda.Aux.Dependencies
import Lean2Agda.Aux.ProcessedExpr
import Lean2Agda.Main.FormatExpr
import Lean2Agda.Passes.FixImplicits
import Lean2Agda.Passes.Dedup

import Lean.Declaration
import Batteries.Data.Vector.Basic
import Lake.Util.EStateT

open Batteries (Vector)
open Std (HashSet)
open Lean (BinderInfo Name Expr Environment MessageData ConstantVal ConstructorVal InductiveVal RecursorVal)
open Lake (EStateT)

private def numImplicitParams (e: Expr) :=
  go e 0
where
  go (e: Expr) (n: Nat) :=
    match e with
      | .forallE _ _ _ (.default) => n
      | .forallE _ _ b _ => go b n.succ
      | .mdata _ e => go e n
      | _ => n

private def TranslateOutput (M: Type → Type) := (Array (Name × GenLevelInstance)) × M Unit

instance [Monad M]: Inhabited (TranslateOutput M) := ⟨⟨Array.empty, pure ()⟩⟩

private structure Visited where
  visitedConstants : HashSet (Name × GenLevelInstance) := {}
  deriving Inhabited

structure TranslateState where
  env : Environment
  modulesState : ModulesState := default
  dedupState : DedupState := {}
  globalNames : GlobalNames := {}
  globalAnalysis: GlobalAnalysis := {}
  visited: Visited := {}

genSubMonad (TranslateState) (GlobalAnalysis) globalAnalysis globalAnalysis
genSubMonad (TranslateState) (GlobalNames) globalNames globalNames
genSubMonad (TranslateState) (DedupState) dedupState dedupState
genSubMonad (TranslateState) (Visited) visited visited
genSubMonad (TranslateState) (ModulesState) modulesState modulesState

instance {M: Type → Type} [Monad M] [base: MonadStateOf TranslateState M] [Value DummyEnvironment]: MonadStateOf Environment M where
    get := do pure (← base.get).env
    modifyGet f := do
      let dummy := (valueOf DummyEnvironment).dummyEnv
      pure (← base.modifyGet (λ σ ↦
        let v := σ.env
        let σ := {σ with env := dummy}
        let (r, σ') := f v
        (r, {σ with env := σ'})
      ))
    set σ' := base.modifyGet (λ σ ↦ ((), {σ with env := σ'}))

abbrev TranslateT := EStateT MessageData TranslateState

local macro "M": term => `(TranslateT IO)

variable [Value Language] [Value DedupData] [Value AnnotateContext] [Value EraseContext] [Value DedupConfig] [Value MetaMContext]

private def fixAndDedupExprsFor
  [Value MetaMContext] [Value DedupConfig]
    (name: Name) (es: Array (Expr × Option Expr × Option Preserve)): M (Array DedupedExpr) := do
  if isDedupConst name then
    pure <| es.map ({ deduped := ·.1 })
  else
    runMetaMMod DedupState do
      -- TODO: pass the type to dedupExprs so we might save some type inference
      let es ← es.mapM (λ (e, ty, preserve) ↦ do pure (⟨← fixExpr e ty, preserve⟩ : (_ × _)))
      dedupExprs es

private def processExprAnd
    (constInstance: ConstInstance) (levelParams: Vector Name constInstance.constAnalysis.numLevels) (e : DedupedExpr) (keep: Nat) (f: [Value BoundLevels] → [Value AnnotationData] → ProcessedExpr → FormatT IO α): StateT Dependencies M α := do
  have := ← getTheValue Environment
  let (e, annotationData) ← processExpr constInstance levelParams e keep

  StateT.run' (s := ({} : ExprState)) do
    have := mkValue annotationData
    have := mkValue <| boundLevels e.constInstance e.erased.levelParams
    liftM (f e)

private def afterDependencies (deps: Dependencies) (m: M Unit): TranslateOutput M :=
  let deps := deps.dependencies.toArray.qsort (Ordering.isLT $ compare · ·)
  ⟨deps, m⟩

private def produceOutput (ci: ConstAnalysis) (deps: Dependencies) (ns: Array String) (m: [Value ModuleState] → M Unit): TranslateOutput M :=
  afterDependencies deps do
    let ms ← getOrOpenOutputModuleForConst ci
    let (_, ms) ← StateT.run (s := ms) do
      goToNamespace ns
    have := mkValue ms
    m

private def translateRecord (constInstance: ConstInstance) (deps: Dependencies) (ns: Array String) (n: String) (val: InductiveVal)
  (typeParams : Array (Option BinderInfo × String × PFormat)) (type: PFormat) (info: String)
  (ctor: ConstructorVal) (fields: Array (Option BinderInfo × String × PFormat))
  : M (TranslateOutput M) := do
  pure <| produceOutput constInstance.constAnalysis deps ns do
    nlprintln s!"--record {info}"
    output $ andWhere (typing (parameterized (kwToken "record" n) (formatParams typeParams).data) type)

    let name ← if dot != '.' then
      stringifyGlobalName ctor.name constInstance.levelInstance
    else
      stringifyUnqualifiedName val.name ctor.name constInstance.levelInstance

    if val.isRec then
      outputIndented 1 $ token "inductive"
    outputIndented 1 $ kwToken "constructor" name

    if !fields.isEmpty then
      outputIndented 1 $ token "field"
      fields.forM fun ⟨bi, n, t⟩ => do
        outputIndented 2 $ typing (encloseWith (maybeLotBinderSeps bi) (token n)) t

private def translateData [Value Environment] (constInstance: ConstInstance) (deps: Dependencies) (ns: Array String) (n: String) (val: InductiveVal)
  (typeParams : Array (Option BinderInfo × String × PFormat)) (type: PFormat) (info: String)
  (ctors : Array ConstructorVal) (ctorTypes : Array DedupedExpr) (typeValues : Array String)

  : M (TranslateOutput M) := do
  let (ctorExprs, deps) ← StateT.run (s := deps) do
    --(ctors.zip ctorTypes).mapM fun (ctor, ctorType) => do
    ctorTypes.mapM fun ctorType => do
      -- levelParams was []
      processExprAnd constInstance constInstance.levelParams ctorType 0 fun e => do
        substTypeParams [] e.erased.expr typeValues formatExprInner

  pure <| produceOutput constInstance.constAnalysis deps ns do
    nlprintln s!"--inductive {info}"
    output $ andWhere (typing (parameterized (kwToken "data" n) (formatParams typeParams).data) type)

    (ctors.zip ctorExprs).forM fun (ctor, expr) => do
      --println s!"--ctor {ctor.numParams} {ctor.numFields}"
      let name ← if dot != '.' then
        stringifyGlobalName ctor.name constInstance.levelInstance
      else
        stringifyUnqualifiedName val.name ctor.name constInstance.levelInstance
      outputIndented 1 $
        typing (token name) expr

    if val.name == `Nat then
      nlprintln "{-# BUILTIN NATURAL Nat #-}"

private def translateInductive (c: Name) (constInstance: ConstInstance) (ns: Array String) (n: String) (val: InductiveVal): M (TranslateOutput M) := do
  let ctors <- val.ctors.toArray.mapM fun ctor => do match ((← getThe Environment).find? ctor |>.get!) with
    | .ctorInfo ctor => pure ctor
    | _ => throw m!"inductive ctor is not a ctor"

  -- invert transformation that transform indices to params, e.g. in Eq
  let fixedNumParams := ctors.foldl (λ v c ↦ v.min (numImplicitParams c.type)) val.numParams

  let es := #[⟨val.type, none, some {kind := .forAllE, n := fixedNumParams}⟩].append <|
    ctors.map (λ c ↦ ⟨c.type, none, some {kind := .forAllE, n := c.numParams + c.numFields}⟩)
  let es ← fixAndDedupExprsFor c es
  let ty := es[0]!
  let ctorTypes := es.extract 1 es.size
  let deps: Dependencies := {}

  have := ← getTheValue Environment
  let numParamsToExtract := val.levelParams.length + fixedNumParams
  let ((typeParams, type), deps) <- StateT.run (s := deps) do
    processExprAnd constInstance constInstance.levelParams ty numParamsToExtract fun processedType => do
      formatParamsAndProcessedExpr processedType numParamsToExtract
  let typeValues := (typeParams.extract constInstance.numSpecializedLevelParams typeParams.size).map (λ (_, s, _) ↦ s)

  let (record, deps) ← StateT.run (s := deps) do
    match (ctors.zip ctorTypes), val.numIndices == 0 with
    | #[⟨ctor, ctorType⟩], true => do
      let numCtorParams := (ctor.levelParams.length + ctor.numParams + ctor.numFields)
      let ctorLevelParams ← toVector ctor.levelParams.toArray constInstance.constAnalysis.numLevels "level parameters in inductive ctor compared to inductive type"
      let (fields, _) <- processExprAnd constInstance ctorLevelParams ctorType numCtorParams fun e => do
        substTypeParams [] e.erased.expr typeValues fun _ms e => do
          formatTypeParamsAndHandleExpr e ctor.numFields true (λ _ _ => pure ())

      -- Agda actually supports implicit and typeclass fields, no need to exclude them!
      --pure $ if fields.all (fun ⟨bi, _, _⟩ => bi == some BinderInfo.default) then
      --  some (ctor, fields)
      --else
      --  none
      pure <| some (ctor, fields)
    | _, _ =>
      pure none

  let info := s!"{val.levelParams.length} {val.numParams}->{fixedNumParams} {val.numIndices} {typeParams.size}"

  match record with
  | .some (ctor, fields) => do
    translateRecord constInstance deps ns n val typeParams type info ctor fields
  | .none =>
    translateData constInstance deps ns n val typeParams type info ctors ctorTypes typeValues

private def translateFun [Value Environment]
    (constInstance: ConstInstance)
    (deps: Dependencies) (ns: Array String) (s: String) (n: String) (kw: Option String) (ty: DedupedExpr) (cases: List PFormat): M (TranslateOutput M) := do
  let (ty, deps) ← StateT.run (s := deps) do
    processExprAnd constInstance constInstance.levelParams ty 0 fun e =>
      let levelParams := specializeLevelParams e.constInstance.constAnalysis e.constInstance.levelInstance e.erased.levelParams
      formatExprInnerWithLevelParams levelParams.toList [] e.erased.expr

  pure <| produceOutput constInstance.constAnalysis deps ns do
    nlprintln s!"--{s}"
    let d := typing (token n) ty
    let d := match kw with
    | .some kw =>
      sect kw d
    | .none =>
      d

    output d
    cases.forM fun s => do
      output s

private def translateRecursor (c: Name) (constInstance: ConstInstance) (ns: Array String) (n: String) (val: RecursorVal): M (TranslateOutput M) := do
  let ctors <- val.rules.mapM fun rule => do match ((← getThe Environment).find? rule.ctor |>.get!) with
    | .ctorInfo ctor => pure ctor
    | _ => throw m!"inductive ctor is not a ctor"

  let fixedNumParams := ctors.foldl (λ v c ↦ v.min (numImplicitParams c.type)) val.numParams
  let fixedNumIndices := val.numIndices + val.numParams - fixedNumParams

  let numGen := val.numParams + val.numMotives + val.numMinors

  let es := #[⟨val.type, none, some {kind := .forAllE, n := val.numParams}⟩].appendList <|
    (val.rules.zip ctors).map (λ (rule, ctor) ↦ ⟨rule.rhs, none, some {kind := .lam, n := numGen + ctor.numFields}⟩)
  let es ← fixAndDedupExprsFor c es
  let ty := es[0]!
  let rulesRhs := (es.extract 1 es.size).toList
  let deps: Dependencies := {}

  have := ← getTheValue Environment
  let ((p, cases), deps) ← StateT.run (s := deps) do
    let (params, _) <- processExprAnd constInstance constInstance.levelParams ty (val.levelParams.length + val.numParams) fun e => do
      formatParamsAndProcessedExpr e (val.levelParams.length + numGen)

    -- TODO: && levelKinds[0]? == some (.pos)
    if val.name == `Acc.rec then
      pure ⟨some "postulate", []⟩
    else
      let cases ← (rulesRhs.zip ctors).mapM fun (ruleRhs, ctor) => do
        let mut ((a, b), ctorConst) <- processExprAnd constInstance constInstance.levelParams ruleRhs (val.levelParams.length + val.numParams) λ e ↦ do
          let ab ← formatArgsWithEagerImplicits ty (· - ctor.numFields + 1 + val.numIndices) e
          let ctorLevelParams := constInstance.levelParams.extract val.numMotives constInstance.levelParams.size
          let ctorConst ← formatConst ctor.name (ctorLevelParams.toArray.map (.param ·)) id false
          pure (ab, ctorConst)

        let numLevelParams := constInstance.numSpecializedLevelParams

        let extraParams := formatArgs (a.extract (numLevelParams + fixedNumParams) (numLevelParams + val.numParams))
        -- fix binder kinds since we don't specify the expected type of the rule rhs when passing to fixAndDedupExprsFor
        for i in [0:params.size] do
          a := a.set! i ⟨(params.get! i).1, (a.get! i).2⟩
        let gen := formatArgs (a.extract 0 (numLevelParams + numGen))
        let indices := (List.range val.numIndices).map fun _ => encloseWith implicitBinderSeps (token "_")
        let fields := formatArgs (a.extract (numLevelParams + numGen) (numLevelParams + numGen + ctor.numFields))
        let extra := formatArgs (a.extract (numLevelParams + numGen + ctor.numFields) a.size)

        let object := enclose "(" (app ctorConst (extraParams ++ fields)) ")"

        pure $ define (app (token n) (gen ++ indices ++ [object] ++ extra)) [b]

      let cases <- if cases.isEmpty then do
        let levels := List.replicate (constInstance.numSpecializedLevelParams) $ encloseWith levelBinderSeps (token "_")
        let genIndices := List.replicate (numGen + fixedNumIndices) $ token " _"
        pure <| [app (token n) (levels ++ genIndices ++ [token "()"])]
      else
        pure cases
      pure (none, cases)

  translateFun constInstance deps ns s!"recursor {val.numParams}->{fixedNumParams} {val.numIndices}->{fixedNumIndices} {val.numMotives} {val.numMinors}" n p ty cases

private def translateDef
    (c: Name) (constInstance: ConstInstance)
    (m: Array String) (s: String) (n: String) (val: ConstantVal) (v: Option Expr) : M (TranslateOutput M) := do
  --dbg_trace s!"dumpDef {c} {val.levelParams} {levelKinds} {v}"
  let es := #[⟨val.type, none, none⟩]
  let es := if let .some v := v then
    es.push ⟨v, val.type, none⟩
  else
    es
  let es ← fixAndDedupExprsFor c es
  let ty := es.get! 0
  let v := es.get? 1
  let deps: Dependencies := {}

  have := ← getTheValue Environment
  let ((p, cases), deps) ← StateT.run (s := deps) do
    if c == `WellFounded.fixFEq then
      pure (some "postulate", [])
    else
      match v with
      | some v => do
        let mut (a, b) ← processExprAnd constInstance constInstance.levelParams v 0 λ e ↦ do
          formatArgsWithEagerImplicits ty id e
        --let (typeParams, _) <- processExprAnd constInstance val.levelParams levelKinds ty a.size fun processedType => do
        --  formatParamsAndHandleExpr processedType a.size false (λ _ _ _ ↦ pure ())
        --for i in [0:typeParams.size.min a.size] do
        --  a := a.set! i ⟨(typeParams.get! i).1, (a.get! i).2⟩

        pure (none, [define (app (token n) (formatArgs a)) [b]])
      | none => do
        pure (some "postulate", [])

  translateFun constInstance deps m s n p ty cases

private def translateConstant'
  (c : Name) (levelInstance: GenLevelInstance): M (Option (Option (TranslateOutput M))) := do
  if (← getThe Visited).visitedConstants.contains (c, levelInstance) then
    return some none

  let r ← try
    let .some val := (← getThe Environment).find? c | throw m!"not found"

    let constAnalysis ← (
      have := ← getTheValue Environment
      getOrComputeConstAnalysis c
    )
    let levelInstance ← toVector levelInstance constAnalysis.numLevelClauses "level kinds in level instance for constant to be translated"
    let levelParams ← toVector val.levelParams.toArray constAnalysis.numLevels "level parameters in constant declaration compared to analysis"
    let .some constInstance := makeConstInstance constAnalysis levelInstance levelParams | return none
    --comment s!"const instance for {c}: {repr constInstance}"

    let (ns, n) ← declarationName c levelInstance

    pure <| some <| some <| ← match val with
    | .axiomInfo val => do
      translateDef c constInstance ns "axiom" n val.toConstantVal none
    | .defnInfo val => do
      translateDef c constInstance ns "def" n val.toConstantVal (some val.value)
    | .thmInfo val => do
      translateDef c constInstance ns "theorem" n val.toConstantVal (some val.value)
    | .opaqueInfo val  =>
      translateDef c constInstance ns "opaque" n val.toConstantVal (some val.value)
    | .quotInfo val =>
      translateDef c constInstance ns "quot" n val.toConstantVal none
    | .inductInfo val => do
      translateInductive c constInstance ns n val
    | .ctorInfo _ =>
      pure (#[], pure ())
    | .recInfo val =>
      translateRecursor c constInstance ns n val
  catch e =>
    throw m!"translating constant {c}\n{e}"

  modifyThe Visited λ ({visitedConstants}) ↦ {visitedConstants := visitedConstants.insert (c, levelInstance) }
  pure r

private inductive QueueItem
| const (c: Name) (levelInstance: GenLevelInstance)
| out (m: M Unit)

private partial def translateConstantQueue (a: Array QueueItem) (e: Option (TranslateOutput M)): M Unit := do
  let a := match e with
  | .some (deps, out) =>
    let depsItems := deps.map fun (n, levelInstance) => QueueItem.const n levelInstance
    (a.push (.out out)).append depsItems.reverse
  | .none => a

  match a.backPop? with
  | .none => pure ()
  | .some ((.const c levelInstance), a) =>
    match ← translateConstant' c levelInstance with
    | .some e => translateConstantQueue a e
    | .none => throw m!"attempted to reference constant {c} with impossible level instance {levelInstance}!"
  | .some ((.out m), a) =>
    m
    translateConstantQueue a none

@[nospecialize, noinline]
def translateConstant
  (c : Name) (levelInstance: GenLevelInstance): M (Option Unit) := do
  match ← translateConstant' c levelInstance with
  | .none =>
    pure none
  | .some x =>
    translateConstantQueue #[] x
    pure <| some ()

@[nospecialize, noinline]
partial def translateConstantVariants
  (c : Name): M Unit := do
  let constAnalysis ← (
    have := ← getTheValue Environment
    getOrComputeConstAnalysis c
  )
  StateT.run' (s := #[]) do
    go constAnalysis.numLevelClauses
where
  go (n: Nat): StateT GenLevelInstance M Unit := do
    match n with
    | .zero =>
      let _ ← translateConstant c (← getThe GenLevelInstance)
    | .succ n =>
      #[false, true].forM fun b => do
        modifyThe GenLevelInstance (·.push b)
        go n
        modifyThe GenLevelInstance (·.pop)
