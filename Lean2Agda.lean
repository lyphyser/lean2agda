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
import Lean2Agda.RunMetaM

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

deriving instance Hashable, Repr for ModuleIdx

variable {M : Type → Type} [Monad M] [MonadExceptOf MessageData M]

local instance [MonadStateOf α M]: MonadReaderOf α M where
  read := get

local instance [Repr α]: ToFormat α where
  format := repr

structure Config extends EraseConfig where
  options: Options := {}

structure Context extends Config, EraseContext, AnnotateContext, DedupConfig, MetaMContext where
  keywords : HashSet String
  implicitKeyword: Name

genSubReader (Context) (AnnotateContext) toAnnotateContext
genSubReader (Context) (MetaMContext) toMetaMContext
genSubReader (Context) (EraseContext) toEraseContext
genSubReader (Context) (DedupConfig) toDedupConfig

structure HygienicNames where
  hygienicNames: HashMap String Nat := {}
  deriving Inhabited

structure GlobalNames where
  hygienicNames: HygienicNames := {}
  nameReplacements: HashMap Name String := {}
  deriving Inhabited

genSubMonad (GlobalNames) (HygienicNames) hygienicNames hygienicNames

structure ExprState where
  hygienicNames: HygienicNames := {}
  patternNames: HashMap String Nat := {}
  bvarValues : Array String := {}
  deriving Inhabited

genSubMonad (ExprState) (HygienicNames) hygienicNames hygienicNames

abbrev GenLevelInstance := Array Bool
abbrev LevelInstance (n: Nat) := Vector Bool n

structure Dependencies where
  dependencies: HashSet (Name × GenLevelInstance) := {}
  deriving Inhabited

structure Visited where
  visitedConstants : HashSet (Name × GenLevelInstance) := {}
  deriving Inhabited

structure ModuleState where
  curNamespace: Array String := {}
  indentSpace: Nat := 0
  output: IO.FS.Stream
  deriving Inhabited

def ModulesState := Option ModuleState
  deriving Inhabited

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

instance : Coe α (M α) where
  coe := pure

instance : Coe (Id α) (M α) where
  coe := pure

def M.run
  (config : Config) (env : Environment) (act : OurM α) : IO α := do
  let rand := (String.mk $ ← (List.replicate 16 ' ').mapM fun _ => do pure $ Char.ofNat $ ← IO.rand 33 126)
  let projectKeyword := Name.str Name.anonymous ("$$project_" ++ rand)
  let implicitKeyword := Name.str Name.anonymous ("$$implicit_" ++ rand)
  let dedupPrefix := Name.str Name.anonymous ("$$dedup_" ++ rand)
  let binderMDatas := Vector.ofFn (λ i: Fin 4 ↦ KVMap.empty.setInt implicitKeyword i)
  let dummyEnv ← mkEmptyEnvironment
  let keywords: HashSet String := HashSet.empty.insertMany [
    "abstract", "codata", "coinductive", "data", "eta-equality", "field",
    "forall", "hiding", "import", "inductive", "infix", "infixl",
    "infixr", "instance", "let", "macro", "module", "mutual",
    "open", "overlap", "pattern", "postulate", "primitive",
    "private", "public", "quote", "quoteContext", "quoteGoal",
    "quoteTerm", "record", "renaming", "rewrite", "syntax",
    "tactic", "unquote", "unquoteDecl", "unquoteDef", "using", "where",
    "with"
  ]

  let r ← StateT.run' (s := ({ env } : _root_.State)) do
    ReaderT.run (r := { config with dummyEnv, keywords, projectKeyword, implicitKeyword, binderMDatas, dedupPrefix}) do
      ExceptT.run do
        act

  match r with
  | Except.error msg => throw <| IO.userError (← msg.toString)
  | Except.ok a => pure a

def fixAndDedupExprsFor [MonadReaderOf Context M] [MonadStateOf Environment M] [MonadStateOf DedupState M]
     [MonadLiftT IO M]
    (name: Name) (es: Array (Expr × Option Expr × Option Preserve)): M (Array DedupedExpr) := do
  if ← isDedupConst name then
    pure <| es.map ({ deduped := ·.1 })
  else
  runMetaMMod DedupConfig DedupState do
    -- TODO: pass the type to dedupExprs so we might save some type inference
    let es ← es.mapM (λ (e, ty, preserve) ↦ do (⟨← fixExpr e ty, preserve⟩ : (_ × _)))
    dedupExprs es

structure ConstInstance where
  constAnalysis: ConstAnalysis
  levelInstance: LevelInstance constAnalysis.numLevelClauses
  levelParams: Vector Name constAnalysis.numLevels
  idx2output: Vector (Option Name) constAnalysis.numLevels
  nonzeroClauses: Array (OrClause (Fin constAnalysis.numLevels))
  deriving Inhabited, Repr

namespace ConstInstance
abbrev numLevels (ci: ConstInstance) := ci.constAnalysis.numLevels
end ConstInstance


structure BoundLevels where
  constInstance: ConstInstance
  input2idx: HashMap Name (Fin constInstance.constAnalysis.numLevels)

  deriving Inhabited, Repr

namespace BoundLevels
abbrev numLevels (b: BoundLevels) := b.constInstance.constAnalysis.numLevels

def isAlwaysZero (b: BoundLevels) (l: Fin b.numLevels): Bool :=
  b.constInstance.idx2output[l].isNone
end BoundLevels

structure ProcessedExpr where
  constInstance: ConstInstance
  erased: ErasedExpr constInstance.constAnalysis.numLevels
  deriving Inhabited
  --levelKinds: Array LevelKind := {}

namespace ProcessedExpr
abbrev numLevels (e: ProcessedExpr) := e.constInstance.constAnalysis.numLevels
end ProcessedExpr

def bindLevelParamsWith [MonadLiftT IO M]
  {α: Type} (ci: ConstInstance) (levelParamValues: Vector Name ci.numLevels) (m: ReaderT BoundLevels M α): M α := do

  let h: levelParamValues.toArray.size = ci.constAnalysis.numLevels := by
    exact levelParamValues.size_eq
  let input2idx := h ▸ reverseHashMap levelParamValues.toArray id id

  let r: BoundLevels := {constInstance := ci, input2idx}
  --traceComment s!"BoundLevels: {repr r}"
  ReaderT.run (r := r) do
    m

def processExprAnd [MonadReaderOf Context M] [MonadStateOf Environment M] [MonadLiftT IO M]
    (constInstance: ConstInstance) (levelParams: Vector Name constInstance.constAnalysis.numLevels) (e : DedupedExpr) (keep: Nat) (f: ProcessedExpr → ReaderT BoundLevels (ReaderT AnnotationData (StateT ExprState M)) α): M α := do
  let e := e.deduped

  have: MonadStateOf Unit M := unitStateOf
  let (e, annotationData) <- runMetaMRo Context Unit do
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

-- not including space or @.(){};_
-- TODO: handle identifiers conflicting with Agda defs
def stringifyIdent [MonadReaderOf Context M]
  (s : String) : M String := do
  let s := s.foldl stringifyIdentAux ""
  if (← read).keywords.contains s then
    "`" ++ s ++ "`"
  else
    s
where stringifyIdentAux (acc : String) (c : Char) : String :=
  if c = '_' then
    acc ++ "-"
  else if c = '.' then
    acc ++ ":"
  else -- TODO: support ⟪⟫ escaped idents
    acc ++ String.singleton c

def usebrokenNamespaceModules := false
def dot := if usebrokenNamespaceModules then '.' else ':'
def intPrefix := if usebrokenNamespaceModules then "$" else ""

/- resolveLevel and applyNonZeroClauses actually do all the work -/
def resolveSimplifiedLevelClause (ci: ConstInstance)
    (c: Option (OrClause (Fin ci.numLevels))): M Bool := do
  match c with
  | .none => true
  | .some #[] => false
  | .some c =>
    throw m!"Unable to decide whether dependent const level clause {c.toArray.map (·.val)} is always nonzero or zero: level clause generation or level resolution is buggy!"

/- apply the fact that e.g. if we know that u OR v != 0, then max(u + 3, v + 6, ...) >= 4, so rewrite the const in the max accordingly -/
def applyNonZeroClauses
  (ci: ConstInstance) (ml: MaxLevel ci.numLevels): MaxLevel ci.numLevels :=
  let {params, const} := ml

  let const := ci.nonzeroClauses.foldl (init := const) λ const c ↦
    let minAdd := c.foldl (init := none) λ m l =>
      some <| match params[l] with
      | .none => 0
      | .some a =>
        match m with
        | .none => a + 1
        | .some m => m.min (a + 1)
    match minAdd with
    | .none => (panic! "nonzero complex clause is empty!") + const
    | .some minAdd => const.max minAdd
  {params, const}

def resolveLevel (b: BoundLevels)
    (l: Level): M (NormLevel b.numLevels) := do
  MaxLevel.normalize <| ← goBuild l
where
  goBuild (l: Level): M (MaxLevel b.numLevels) := do
    let ⟨_, ml⟩ ← StateT.run (s := {const := 0, params := Vector.mkVector b.numLevels none}) (m := M) <|
      go 0 l
    pure <| applyNonZeroClauses b.constInstance ml
  go (add: Nat)
    (l: Level): StateT (MaxLevel b.numLevels) M Unit :=
    match l with
    | .zero => do
      modify (·.maxConst add)
    | .succ l => do
      pure <| (← go (add + 1) l)
    | .param n => do
      if let .some l := b.input2idx.get? n then
        if b.isAlwaysZero l then
          modify (·.maxConst add)
        else
          modify (·.maxParam add l)
      else
        throw m!"unbound level variable {n}"
    | .max l1 l2 => do
      go add l1
      go add l2
    | .imax l1 l2 => do
      let m2 ← goBuild l2

      if (← resolveSimplifiedLevelClause b.constInstance m2.toClause) then
        modify (·.maxMaxLevel add m2)
        go add l1
      else
        modify (·.maxConst add)
    | .mvar _ => throw m!"unexpected mvar in level"

def includeLevelParam (c: ConstAnalysis) (levelInstance: LevelInstance c.numLevelClauses) (i: Fin c.numLevels): Bool :=
  match c.singletonLevelClauses[i] with
  | .some ci =>
    have h := by
      apply Fin.val_lt_of_le
      exact c.numSingletonLevelClauses_le
    levelInstance[ci]'h
  | .none => true

def specializeLevelParams (c: ConstAnalysis) (levelInstance: LevelInstance c.numLevelClauses) (a: Vector α c.numLevels):
  Array α :=
  Fin.foldl c.numLevels (init := Array.empty) λ r i ↦
    if includeLevelParam c levelInstance i then
      r.push a[i]
    else
      r

def numSpecializedLevelParams (c: ConstAnalysis) (levelInstance: LevelInstance c.numLevelClauses): Nat :=
  Fin.foldl c.numLevels (init := 0) λ r i ↦
    if includeLevelParam c levelInstance i then
      r.succ
    else
      r

namespace ConstInstance
def numSpecializedLevelParams (ci: ConstInstance): Nat :=
  _root_.numSpecializedLevelParams ci.constAnalysis ci.levelInstance
end ConstInstance

def myPretty (f : Format) (width : Nat := 150) (indent : Nat := 0) (column := 0) : String :=
  let act : StateM PrettyState Unit := _root_.prettyM f width indent
  PrettyState.out <| act (PrettyState.mk "" column {} 0) |>.snd

open Std.Format in
def outputIndented [MonadReaderOf ModuleState M] [MonadLiftT IO M]
  (levels: Nat) (f: PFormat): M Unit := do
  (← read).output.putStr <| (myPretty <| nest ((← read).indentSpace + levels * indentOneLevelSpaces) <| (text "\n") ++ (resolveWithPrec f .bottom)) ++ "\n"

def output [MonadReaderOf ModuleState M] [MonadLiftT IO M]
  (f: PFormat): M Unit := do
  outputIndented 0 f

def println [MonadReaderOf ModuleState M] [MonadLiftT IO M]
  (s: String) (pfx: String := ""): M Unit := do
  --output (format (text s))
  (← read).output.putStr s!"{pfx.pushn ' ' $ (← read).indentSpace}{s}\n"

def nlprintln [MonadReaderOf ModuleState M] [MonadLiftT IO M]
  (s: String): M Unit := do
  println s (pfx := "\n")

def comment [MonadReaderOf ModuleState M] [MonadLiftT IO M]
  (s: String): M Unit := do
  nlprintln ("--" ++ (s.replace "\n" "\n--"))

def traceComment [MonadLiftT IO M]
  (s: String): M Unit := do
  IO.println ("--" ++ (s.replace "\n" "\n--"))

def makeHygienicName [MonadStateOf HygienicNames M] [MonadReaderOf Context M]
  (v: String) (f: String → M α): M α := do
  let h <- modifyGet (fun s =>
    let h := s.hygienicNames.getD v 0
    (h, {s with hygienicNames := s.hygienicNames.insert v (h + 1)})
  )
  let r <- f s!"{← stringifyIdent v}${if h == 0 then "" else s!"{h}"}"
  modify fun s => {s with hygienicNames := if h == 0 then
      s.hygienicNames.erase v
    else
      s.hygienicNames.insert v h
  }
  pure r

def stringifyUnqualifiedName [MonadStateOf GlobalNames M] [MonadReaderOf Context M]
  (p: Name) (name : Name) {numLevelClauses: Nat} (levelInstance: LevelInstance numLevelClauses): M String := do
  if let .some replacement := (← getThe GlobalNames).nameReplacements.get? name then
    return replacement

  let s ← toName p name ""
  let s := if numLevelClauses = 0 then
    s
  else
    s ++ "#" ++ (String.join $ Vector.toList $ levelInstance.map (fun s => if s == true then "n" else "z"))
  if dot == '.' then
    pure s
  else
    stringifyIdent s
where
  toName (p: Name) (n: Name) (suffix: String): M String := do
    if n == p then
      throw m!"qualified name is equal to namespace: {n}"
    else
      match n with
      | .anonymous => throw m!"qualified name is not in expected namespace"
      | .str v "_@" =>
        let v := s!"{v}"
        let r ← makeHygienicName v (·)
        modifyThe GlobalNames λ {hygienicNames, nameReplacements} ↦ {hygienicNames, nameReplacements := nameReplacements.insert name r}
        r
      | .str n s =>
        let s ← if dot == '.' then
          stringifyIdent s
        else
          s
        toNameDot p n s!"{s}{suffix}"
      | .num n i =>
        if n == (← read).dedupPrefix then
          s!"#{i}"
        else
          toNameDot p n s!"{intPrefix}{i}{suffix}"
  toNameDot (p: Name) (n: Name) (suffix: String): M String :=
    if n == p then
      suffix
    else
      toName p n s!"{dot}{suffix}"

def stringifyGlobalName [MonadStateOf GlobalNames M] [MonadReaderOf Context M]
  (n : Name) {numLevelClauses: Nat} (levelInstance: LevelInstance numLevelClauses): M String :=
  match n with
  | .anonymous => throw m!"anonymous global name"
  | _ => stringifyUnqualifiedName Name.anonymous n levelInstance

def nameToArray [MonadReaderOf Context M]
  (n : Name) : M (Array String) := do
  (← go n Array.empty).reverse
where go (n: Name) (a: Array String): M (Array String) := do
  match n with
  | .anonymous => a
  | .str n s => go n (a.push (← stringifyIdent s))
  | .num n i => go n (a.push s!"{intPrefix}{i}")

def declarationName [MonadStateOf GlobalNames M] [MonadReaderOf Context M]
  (n : Name) {numLevelClauses: Nat} (levelInstance: LevelInstance numLevelClauses) : M (Array String × String) := do
  if usebrokenNamespaceModules then
    let a := ← nameToArray n
    let n := a.back?
    let a := a.pop
    pure $ (a, match n with
    | none => "_"
    | some s => s)
  else
    pure $ (#[], ← stringifyGlobalName n levelInstance)

def goToNamespace [MonadStateOf ModuleState M] [MonadLiftT IO M]
  (a : Array String) : M Unit := do
  if usebrokenNamespaceModules then
    let p := commonPrefixLength (← get).curNamespace a
    modify fun s => {s with curNamespace := s.curNamespace.extract 0 p, indentSpace := p * indentOneLevelSpaces}
    (a.extract p a.size).forM openModule
where openModule (m: String): M Unit := do
  nlprintln s!"module {m} where"
  modify fun s => {s with curNamespace := s.curNamespace.push m, indentSpace := indentOneLevelSpaces}

def formatLevel [MonadReaderOf Context M]
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

def escape (s : String) : String :=
  s.foldl escapeAux ""
where escapeAux (acc : String) (c : Char) : String :=
  -- escape ", \, \n and \r, keep all other characters ≥ 0x20 and render characters < 0x20 with \u
  if c = '"' then -- hack to prevent emacs from regarding the rest of the file as a string: "
    acc ++ "\\\""
  else if c = '\\' then
    acc ++ "\\\\"
  else if c = '\n' then
    acc ++ "\\n"
  else if c = '\x0d' then
    acc ++ "\\r"
  -- the c.val ≤ 0x10ffff check is technically redundant,
  -- since Lean chars are unicode scalar values ≤ 0x10ffff.
  -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
  -- the JSON standard is not definite: both directly printing the character
  -- and encoding it with multiple \u is allowed, and it is up to parsers to make the
  -- decision.
  else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
    acc ++ String.singleton c
  else
    let n := c.toNat;
    -- since c.val < 0x20 in this case, this conversion is more involved than necessary
    -- (but we keep it for completeness)
    acc ++ "\\u" ++
    [ Nat.digitChar (n / 4096),
      Nat.digitChar ((n % 4096) / 256),
      Nat.digitChar ((n % 256) / 16),
      Nat.digitChar (n % 16) ].asString

def withLocalName [MonadStateOf ExprState M] [MonadReaderOf Context M]
  {α: Type} [Inhabited α] (name : Name) (pattern: Bool) (f: String → M α): M α :=
  go name false f
where
  go (n: Name) (inside: Bool) (f: String → M α): M α := do
    match n with
    | .anonymous =>
      if inside then
        throw m!"unexpected local name {name}"
      else
        f "_"
    | .str Name.anonymous v => do
      if inside then
        throw m!"unexpected local name {name}"
      else if pattern then
        let h <- modifyGet (fun s =>
          let h := s.patternNames.getD v 0
          (h, {s with patternNames := s.patternNames.insert v (h + 1)})
        )
        let r ← f s!"{← stringifyIdent v}{if h == 0 then "" else if h == 1 then "#" else s!"#{h - 1}"}"
        modify fun s => {s with patternNames := if h == 0 then
            s.patternNames.erase v
          else
            s.patternNames.insert v h
        }
        pure r
      else
        f (← stringifyIdent v)
    | .str v "_@" => do
      let v := s!"{v}"
      makeHygienicName v f
    | .str n _ => go n true f
    | .num n _ => go n true f

def bindStr [MonadStateOf ExprState M]
  {α: Type} [Inhabited α] (n: String) (e: M α): M (String × α) := do
  modify fun s => {s with bvarValues := s.bvarValues.push n }
  let v <- e
  modify fun s => {s with bvarValues := s.bvarValues.pop }
  return (n, v)

def bindIf [MonadStateOf ExprState M] [MonadReaderOf Context M]
  {α: Type} [Inhabited α] (pattern: Bool) (n: Name) (e: M α): M (String × α) := do
  withLocalName n pattern (bindStr · e)

def bind [MonadStateOf ExprState M] [MonadReaderOf Context M]
  {α: Type} [Inhabited α] (n: Name) (e: M α): M (String × α) :=
  -- TODO: implement proper name liveness analysis
  --bindIf false n e
  bindIf true n e

def addDependency [MonadStateOf Dependencies M]
  (n: Name) (levelInstance: GenLevelInstance): M Unit := do
  modify fun st => { st with dependencies := st.dependencies.insert (n, levelInstance)}

def argName: Expr → Nat → M Name
| .forallE n _ _ _, .zero => n
| .forallE _ _ b _, .succ n => argName b n
| .mdata _ e, n => argName e n
| _, _ => throw m!"argument not found!"

def extractLevelParams [MonadStateOf ExprState M] [MonadReaderOf Context M]
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

def formatLevelParams [MonadStateOf ExprState M] [MonadReaderOf Context M]
  (l: List Name) : M (Array PFormat) := do
  let (params, _) <- extractLevelParams l l.length
  pure $ formatParams params


section FormatExpr
variable
  [MonadLiftT IO M] [MonadStateOf GlobalAnalysis M] [MonadStateOf GlobalNames M] [MonadStateOf Dependencies M] [MonadStateOf ExprState M]
  [MonadReaderOf BoundLevels M] [MonadReaderOf AnnotationData M] [MonadReaderOf Environment M] [MonadReaderOf Context M]

abbrev FormatT (M: Type → Type) [Monad M] := ExceptT MessageData <|
  ReaderT BoundLevels <| ReaderT AnnotationData <| ReaderT Environment <| ReaderT Context <|
  StateT GlobalAnalysis <| StateT GlobalNames <| StateT Dependencies <| StateT ExprState <| M

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
    app c levels
  else
    c

def formatExprInner
  (mdatas: List MData) (e : Expr) : M PFormat := do
  try
    ← goWithMData mdatas e
  catch err =>
    throw m!"in expression {e}\n{err}"
where
  go (e : Expr) := goWithMData [] e

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
    let implicitKeyword := (← read).implicitKeyword
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
    | .lit (.strVal s) => token s!"\"{escape s}\""
    | .mdata m e => goWithMData (m :: mdatas) e

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
  let annotationData <- readThe AnnotationData
  let environment ← readThe Environment
  let context ← readThe Context

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
      ReaderT.run (r := context) do
      ReaderT.run (r := environment) do
      ReaderT.run (r := annotationData) do
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
      | e => pure ⟨← Meta.whnf (e.instantiateRev fvars), #[]⟩
    match e with
    | .forallE n d b bi => do
      Meta.withLocalDecl n bi (d.instantiateRev fvars) fun fv => do
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

end FormatExpr

def substTypeParams [MonadStateOf ExprState M] [MonadReaderOf Context M]
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

def numImplicitParams (e: Expr) :=
  go e 0
where
  go (e: Expr) (n: Nat) :=
    match e with
      | .forallE _ _ _ (.default) => n
      | .forallE _ _ b _ => go b n.succ
      | .mdata _ e => go e n
      | _ => n

section Translate
variable
  [MonadStateOf GlobalAnalysis M] [MonadStateOf GlobalNames M] [MonadStateOf Visited M] [MonadStateOf Environment M] [MonadStateOf DedupState M] [MonadStateOf ModulesState M]
  [MonadReaderOf Context M] [MonadLiftT IO M]

def TranslateOutput (M: Type → Type) := (Array (Name × GenLevelInstance)) × M Unit

instance: Inhabited (TranslateOutput M) := ⟨⟨Array.empty, pure ()⟩⟩

def appendSuffixDirToPath (path: FilePath) (name: Name): FilePath :=
  match name with
  | .anonymous => path
  | .str _ s => path / s
  | .num _ n => path / (toString n)

def appendSuffixFNameToPath (path: FilePath) (name: Name): FilePath :=
  let ext := ".agda"
  match name with
  | .anonymous => path
  | .str _ s => path / (s ++ ext)
  | .num _ n => path / ((toString n) ++ ext)

mutual
  def appendPrefixToPath (path: FilePath) (name: Name): FilePath :=
    match name with
    | .anonymous => path
    | .str p _ => appendToPath path p
    | .num p _ => appendToPath path p

  def appendToPath (path: FilePath) (name: Name): FilePath :=
    appendSuffixDirToPath (appendPrefixToPath path name) name
end

def outputModulePrelude [MonadReaderOf ModuleState M]: M Unit := do
  println "{-# OPTIONS --prop --type-in-type #-}"
  println "open Agda.Primitive" -- TODO: fix this since it could conflict with Lean
  println ""
  println "Type : (u : Level) → Set (lsuc (lsuc u))"
  println "Type u = Set (lsuc u)"
  println ""
  println "lone : Level"
  println "lone = lsuc lzero"

def getOrOpenOutputModuleForConst [MonadStateOf ModulesState M] [MonadReaderOf Environment M] [MonadReaderOf Context M] [MonadLiftT IO M]
  (_ci: ConstAnalysis): M ModuleState := do
  match ← getThe ModulesState with
  | .some ms => ms
  | .none =>
    let output ← (IO.getStdout : IO _)
    let ms: ModuleState := {output}
    ReaderT.run (r := ms) do
      outputModulePrelude

    let mses: ModulesState := (some ms : ModulesState)
    set mses
    ms

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
        [app (token n) (levels ++ genIndices ++ [token "()"])]
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

def makeConstInstance (c: ConstAnalysis) (levelInstance: LevelInstance c.numLevelClauses) (levelParams: Vector Name c.numLevels): Option ConstInstance :=
  let idx2output := Fin.foldl c.numLevelClauses (init := Vector.ofFn λ i ↦ some levelParams[i]) λ v i ↦
    if levelInstance[i] = false then
      c.levelClauses[i].foldl (init := v) λ v l ↦ v.set l none
    else
      v

  let nonzeroClauses := Fin.foldl c.numLevelClauses (init := #[]) λ s i ↦
    if levelInstance[i] = true then
      let cl := c.levelClauses[i]
      s.push <| cl.filter (idx2output[·].isSome)
    else
      s

  let nonzeroClauses := nonzeroClauses.sortDedup

  if nonzeroClauses.contains #[] then
    none
  else
    some <| {constAnalysis := c, levelInstance, levelParams, idx2output, nonzeroClauses}

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

    some <| some <| ← match val with
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
  r

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
  | .none, _ => ()
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
    some ()

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

end Translate
