import Lean2Agda.Analysis.ConstAnalysis
import Lean2Agda.Aux.ConstInstance
import Lean2Agda.Aux.ModulesState
import Lean2Agda.Aux.Dependencies
import Lean2Agda.Aux.ProcessedExpr
import Lean2Agda.Main.FormatExpr
import Lean2Agda.Passes.FixAndDedup

import Lean.Declaration

open Std (HashSet)
open Lean (Name Expr Environment MessageData ConstantVal InductiveVal RecursorVal)

private def numImplicitParams (e: Expr) :=
  go e 0
where
  go (e: Expr) (n: Nat) :=
    match e with
      | .forallE _ _ _ (.default) => n
      | .forallE _ _ b _ => go b n.succ
      | .mdata _ e => go e n
      | _ => n

structure Visited where
  visitedConstants : HashSet (Name × GenLevelInstance) := {}
  deriving Inhabited

variable {M: Type → Type} [Monad M] [MonadExceptOf MessageData M]

variable [MonadLiftT IO M]
  [MonadStateOf GlobalAnalysis M] [MonadStateOf GlobalNames M] [MonadStateOf Visited M] [MonadStateOf Environment M] [MonadStateOf DedupState M] [MonadStateOf ModulesState M]
  [MonadReaderOf Language M] [MonadReaderOf DedupData M] [MonadReaderOf AnnotateContext M] [MonadReaderOf EraseContext M] [MonadReaderOf DedupConfig M] [MonadReaderOf MetaMContext M]

instance: MonadReaderOf Environment M := monadReaderOfOfMonadStateOf

def TranslateOutput (M: Type → Type) := (Array (Name × GenLevelInstance)) × M Unit

instance: Inhabited (TranslateOutput M) := ⟨⟨Array.empty, pure ()⟩⟩

def afterDependencies (deps: Dependencies) (m: M Unit): TranslateOutput M :=
  let deps := deps.dependencies.toArray.qsort (Ordering.isLT $ compare · ·)
  ⟨deps, m⟩

def produceOutput (ci: ConstAnalysis) (deps: Dependencies) (ns: Array String) (m: ReaderT ModuleState M Unit): TranslateOutput M :=
  afterDependencies deps do
    let ms ← getOrOpenOutputModuleForConst ci
    let (_, ms) ← StateT.run (s := ms) do
      goToNamespace ns
    ReaderT.run (r := ms)
      m

def translateInductive (c: Name) (constInstance: ConstInstance) (ns: Array String) (n: String) (val: InductiveVal): M (TranslateOutput M) := do
  let env ← getThe Environment
  let ctors <- val.ctors.toArray.mapM fun ctor => do match (env.find? ctor |>.get!) with
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

  match record with
  | .some (ctor, fields) => do

    pure <| produceOutput constInstance.constAnalysis deps ns do
      nlprintln s!"--record {val.levelParams.length} {val.numParams}->{fixedNumParams} {val.numIndices} {typeParams.size}"
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

  | .none =>
    let (ctorExprs, deps) ← StateT.run (s := deps) do
      --(ctors.zip ctorTypes).mapM fun (ctor, ctorType) => do
      ctorTypes.mapM fun ctorType => do
        -- levelParams was []
        processExprAnd constInstance constInstance.levelParams ctorType 0 fun e => do
          substTypeParams [] e.erased.expr typeValues formatExprInner

    pure <| produceOutput constInstance.constAnalysis deps ns do
      nlprintln s!"--inductive {val.levelParams.length} {val.numParams}->{fixedNumParams} {val.numIndices} {typeParams.size}"
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

def translateFun
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

def translateRecursor (c: Name) (constInstance: ConstInstance) (ns: Array String) (n: String) (val: RecursorVal): M (TranslateOutput M) := do
  let env ← getThe Environment
  let ctors <- val.rules.mapM fun rule => do match (env.find? rule.ctor |>.get!) with
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

def translateDef
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

  let ((p, cases), deps) ← StateT.run (s := deps) do
    if c == `WellFounded.fixFEq then
      pure (some "postulate", [])
    else
      match v with
      | some v => do
        let mut (a, b) ← processExprAnd constInstance constInstance.levelParams v 0 <|
          formatArgsWithEagerImplicits ty (·)
        --let (typeParams, _) <- processExprAnd constInstance val.levelParams levelKinds ty a.size fun processedType => do
        --  formatParamsAndHandleExpr processedType a.size false (λ _ _ _ ↦ pure ())
        --for i in [0:typeParams.size.min a.size] do
        --  a := a.set! i ⟨(typeParams.get! i).1, (a.get! i).2⟩

        pure (none, [define (app (token n) (formatArgs a)) [b]])
      | none => do
        pure (some "postulate", [])

  translateFun constInstance deps m s n p ty cases

@[noinline, nospecialize]
def translateConstant'
  (c : Name) (levelInstance: GenLevelInstance): M (Option (Option (TranslateOutput M))) := do
  if (← getThe Visited).visitedConstants.contains (c, levelInstance) then
    return some none

  let r ← try
    let env := ← getThe Environment
    let .some val := env.find? c | throw m!"not found"

    let constAnalysis ← getOrComputeConstAnalysis c
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

variable (M) in
inductive QueueItem
| const (c: Name) (levelInstance: GenLevelInstance)
| out (m: M Unit)

@[noinline, nospecialize]
partial def translateConstantQueue (a: Array (QueueItem M)) (e: Option (TranslateOutput M)): M Unit := do
  let a := match e with
  | .some (deps, out) =>
    let depsItems := deps.map fun (n, levelInstance) => QueueItem.const n levelInstance
    (a.push (.out out)).append depsItems.reverse
  | .none => a

  let item := a.back?
  match item, a.pop with
  | .none, _ => pure ()
  | .some (.const c levelInstance), a =>
    match ← translateConstant' c levelInstance with
    | .some e => translateConstantQueue a e
    | .none => throw m!"attempted to reference constant {c} with impossible level instance {levelInstance}!"
  | .some (.out m), a =>
    m
    translateConstantQueue a none

@[noinline, nospecialize]
def translateConstant
  (c : Name) (levelInstance: GenLevelInstance): M (Option Unit) := do
  match ← translateConstant' c levelInstance with
  | .none =>
    pure none
  | .some x =>
    translateConstantQueue #[] x
    pure <| some ()

@[noinline, nospecialize]
partial def translateConstantVariants
  (c : Name): M Unit := do
  let constAnalysis ← getOrComputeConstAnalysis c
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
