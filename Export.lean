-- fix remaining compilation errors from LevelKinds -> LevelInstance change
-- compute the LevelInstance for the constructor pattern in recursor properly (by reusing the .const code?)
-- check that it still works
-- check that places where levelParams was [] and changed still work
-- maybe put processExprAnd and bindLevelParams together
-- split into multiple files

import Pretty

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

namespace Std.HashSet
@[inline]
protected def ofArray [BEq α] [Hashable α] (as : Array α) : HashSet α :=
  HashSet.empty.insertMany as
end Std.HashSet

variable {M : Type → Type} [Monad M] [MonadExceptOf MessageData M]

def toVector (a: Array α) (n: Nat) (desc: String): M (Vector α n) := do
  if h: a.size = n then
    pure ⟨a, h⟩
  else
    throw m!"incorrect number of {desc}: {a.size} instead of {n}"

namespace Batteries.Vector
def mapM {α β} (f : α → M β) (v : Vector α n) : M (Vector β n) := do
  toVector (← v.toArray.mapM f) n "elements produced by mapM on Vector"
end Batteries.Vector

def reverseHashMap {α} (a: Array α) {β} [BEq β] [Hashable β] (f: α → β) {γ} (g: Fin a.size → γ): HashMap β γ:=
  Fin.foldl a.size (init := Std.HashMap.empty) λ m i ↦
    m.insert (f a[i]) (g i)

def reverseVector {α} (a: Array α) {n: Nat} (f: α → Fin n) {γ} (init: γ) (g: Fin a.size → γ): Vector γ n :=
  Fin.foldl a.size (init := Vector.mkVector n init) λ m i ↦
    m.set (f a[i]) (g i)

instance [Repr α]: ToFormat α where
  format := repr

def unitStateOf: MonadStateOf PUnit M where
  get := pure ()
  set _ := pure ()
  modifyGet f := pure (f ()).1

instance [MonadStateOf α M]: MonadReaderOf α M where
  read := get

abbrev OrClause (α) := Array α

namespace OrClause
def toArray (c: OrClause α): Array α :=
  c

def single (x: α): OrClause α :=
  #[x]

def nonTrivial? (c: Option (OrClause α)): Option (OrClause α) :=
  match c with
  | .none => .none
  | .some c =>
    if c.isEmpty then
      none
    else
      some c

def single? (c: OrClause α): Option α :=
  match c with
  | #[v] => some v
  | _ => none

def isFalse (c: OrClause α): Bool :=
  c.isEmpty

def exclude [BEq α] [Hashable α] (c: OrClause α) (s: HashSet α): OrClause α :=
  c.filter (!s.contains ·)

structure Builder (α) where
  duplicated: Array α

namespace Builder
def False: Builder α := {duplicated := #[]}
def True?: Option (Builder α) := none
def False?: Option (Builder α) := some False

def or (b: Builder α) (x: α): Builder α :=
  let {duplicated} := b
  {duplicated := duplicated.push x}

def or? (b: Option (Builder α)) (x: α): Option (Builder α) :=
  b.map (·.or x)

def orClause (b: Builder α) (c: OrClause α): Builder α :=
  let {duplicated} := b
  {duplicated := duplicated.append c}

def orClause? (b: Builder α): Option (OrClause α) → Option (Builder α)
| .some c => some <| b.orClause c
| _ => none

def orClause??: Option (Builder α) → Option (OrClause α) → Option (Builder α)
| .some b, .some c => some <| b.orClause c
| _, _ => none

def orBool?: Option (Builder α) →  Bool → Option (Builder α)
| b, false => b
| _, true => none

def build [Ord α] (b: Builder α): OrClause α :=
  let {duplicated} := b
  duplicated.sortDedup

def build? [Ord α] (b: Option (Builder α)): Option (OrClause α) :=
  b.map (·.build)

-- must be a subset of another clauses, with elements added in the same order!
def buildSubset [Ord α] (b: Builder α): OrClause α :=
  let {duplicated} := b
  duplicated

def buildSubset? [Ord α] (b: Option (Builder α)): Option (OrClause α) :=
  b.map (·.buildSubset)

end Builder

def filter (cs: OrClause α) (f: α → Bool): OrClause α :=
  Array.filter f cs

def union [Ord α] (cs: Array (OrClause α)): OrClause α :=
  (cs.foldl (·.orClause ·) Builder.False).build

def subst [Ord α] {n: Nat} (c: OrClause (Fin n)) (rs: Vector (Option (OrClause α)) n): Option (OrClause α) :=
  Builder.build? (c.foldl (λ b i ↦ Builder.orClause?? b (rs.get i)) (some Builder.False))
end OrClause

structure EraseConfig where
  eraseLambdaTypes: Bool := false
  omitImplicits: Bool := false

structure Config extends EraseConfig where
  options: Options := {}

structure DedupConfig where
  options: Options
  dedupPrefix: Name

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

structure ExprTyStructEq where
  val : ExprStructEq
  ty : Option ExprStructEq
  deriving Inhabited, BEq, Hashable

open Lean.Meta in
/-- Correct implicitness of lambdas -/
partial def fixExpr [MonadLiftT MetaM M] [MonadControlT MetaM M]
    (input : Expr)
    (expectedType : Option Expr )
    (usedLetOnly := false)
    : M Expr := do
  let _ : STWorld IO.RealWorld M := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) M := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }

  let rec visit (e : Expr) (ty : Option Expr) : MonadCacheT ExprTyStructEq Expr M Expr :=
    checkCache { val := e, ty : ExprTyStructEq } fun _ => Meta.withIncRecDepth do
      let rec visitLambda (fvars : Array Expr) (e : Expr) (ty: Option Expr): MonadCacheT ExprTyStructEq Expr M Expr := do
        match e with
        | Expr.lam n d b c =>
          let (bt, c) ← match ty with
          | .none => pure (none, c)
          | .some ty =>
            let ty ← whnf ty
            match ty with
            | .forallE n' d' b' c' =>
              withLocalDecl n' c' d' fun x =>
                pure (some (b'.instantiate1 x), c')
            | _ =>
              throw m!"pi type expected\nexpression: {indentExpr e}\nexpected type: {indentExpr ty}"
              pure (none, c)
          withLocalDecl n c (← visit (d.instantiateRev fvars) none) fun x =>
            visitLambda (fvars.push x) b bt
        | e => mkLambdaFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars) ty)
      let rec visitForall (fvars : Array Expr) (e : Expr) : MonadCacheT ExprTyStructEq Expr M Expr := do
        match e with
        | Expr.forallE n d b c =>
          withLocalDecl n c (← visit (d.instantiateRev fvars) none) fun x =>
            visitForall (fvars.push x) b
        | e => mkForallFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars) none)
      let rec visitLet (fvars : Array Expr) (e : Expr) : MonadCacheT ExprTyStructEq Expr M Expr := do
        match e with
        | Expr.letE n t v b _ =>
          let ty ← visit (t.instantiateRev fvars) none
          withLetDecl n ty (← visit (v.instantiateRev fvars) (some ty)) fun x =>
            visitLet (fvars.push x) b
        | e => mkLetFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars) none)
      match e with
      | .forallE .. => visitForall #[] e
      | .lam .. => visitLambda #[] e ty
      | .letE .. => visitLet #[] e
      | .app f b =>
        let f := ← visit f none
        let mut ft := none
        match ← whnf (← inferType f) with
          | .forallE _ d _ _ =>
            ft := some d
          | _ => throw m!"function expected: {indentExpr e}"
        let b := ← visit b ft
        pure <| e.updateApp! f b
      | .mdata _ b => pure <| e.updateMData! (← visit b ty)
      | .proj _ _ b => pure <| e.updateProj! (← visit b none)
      | e => pure e
  /-
  let visit' (e : Expr) (ty : Option Expr) : MonadCacheT ExprTy Expr m Expr := do
    let ty ← match ty with
    | .some ty => pure <| some (← visit ty none)
    | .none => pure none
    visit e ty
  -/
  visit input expectedType |>.run

instance {α : Type u} [Ord α] : Ord (Array α) where
  compare x y :=
    let rec loop (i : Nat) : Ordering :=
      if h₁ : i < x.size then
        if h₂ : i < y.size then
          let xi := x[i]'h₁
          let yi := y[i]'h₂
          match compare xi yi with
          | Ordering.eq   => loop (i + 1)
          | result        => result
        else
          Ordering.gt
      else if i < y.size then
        Ordering.lt
      else
        Ordering.eq
    loop 0

instance [Ord α] [Ord β] : Ord (α × β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

def commonPrefixLength {α : Type} [BEq α] (arr1 arr2 : Array α) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if h1: i < arr1.size then
      if h2: i < arr2.size then
        if arr1[i]'h1 == arr2[i]'h2 then
          loop (i + 1)
        else
          i
      else
        i
    else
      i
  loop 0

def compareName : Name → Name → Ordering
  | Name.anonymous, Name.anonymous => Ordering.eq
  | Name.anonymous, _ => Ordering.lt
  | _, Name.anonymous => Ordering.gt
  | Name.num n1 i1, Name.num n2 i2 =>
    match compareName n1 n2 with
    | Ordering.eq => compare i1 i2
    | r => r
  | Name.num _ _, _     => Ordering.lt
  | _, Name.num _ _     => Ordering.gt
  | Name.str n1 s1, Name.str n2 s2 =>
    match compareName n1 n2 with
    | Ordering.eq => compare s1 s2
    | r => r

instance : Ord Name where
  compare n1 n2 := compareName n1 n2

instance : LT Name where
  lt n1 n2 := compareName n1 n2 == Ordering.lt

structure AnnotationData where
  projectionLevels: Array (List Level) := #[]
  deriving Inhabited

structure EraseContext extends EraseConfig where
  projectKeyword: Name

structure EraseState where
  usedBVars: Array Bool := Array.empty
  usedLevels: HashSet Name := {}

structure ErasedExpr (numLevels: Nat) where
  levelParams: Vector Name numLevels
  expr: Expr := (.sort .zero)

instance (numLevels: Nat): Inhabited (ErasedExpr numLevels) :=
  ⟨{levelParams := Vector.mkVector numLevels Name.anonymous}⟩

-- TODO: maybe should cache (but we now have dedup in front so...)
def eraseUnused {numLevels: Nat} (ctx: EraseContext) (annotationData: AnnotationData) (levelParams: Vector Name numLevels) (e : Expr) (keep: Nat): ErasedExpr numLevels :=
  let (expr, s) :=
    Id.run do
      StateT.run (s := {}) do
        go e (keep - numLevels)
  let levelParams := Vector.ofFn λ i => if i < keep || s.usedLevels.contains levelParams[i] then levelParams[i] else Name.anonymous
  {levelParams, expr}
where
  go (e : Expr) (u: Nat) := goWithMData [] e u

  goWithMData (mdatas: List MData) (e : Expr) (u: Nat): StateM EraseState Expr := do
    match e with
    | .bvar i =>
      modify fun s => (
        let a := s.usedBVars
        let i := a.size - 1 - i
        {s with usedBVars := a.set! i true}
      )
      pure e
    | .app f b =>
      pure $ e.updateApp! (← go f 0) (← go b 0)
    | .lam n d b bi =>
      let d ← if ctx.eraseLambdaTypes then
        pure $ .const Name.anonymous []
      else
        go d 0
      let (n', b) <- bind n u b
      pure $ if n' == n then
        e.updateLambda! bi d b
      else
        .lam n' d b bi
    | .letE n d v b nonDep =>
      let d <- go d 0
      let (n', b) <- bind n u b
      pure $ if n' == n then
        e.updateLet! d v b
      else
        .letE n' d v b nonDep
    | .forallE n d b bi =>
      let d <- go d 0
      let (n', b) <- bind n u b
      pure $ if n' == n then
        e.updateForall! bi d b
      else
        .forallE n' d b bi
    | .mdata m b =>
      pure $ e.updateMData! (← goWithMData (m :: mdatas) b u)
    | .proj _ _ b =>
      let projectKeyword := ctx.projectKeyword
      let projId: Option Nat := mdatas.findSome? (·.get? projectKeyword)
      if let .some projId := projId then
        let projectionLevels: List Level := annotationData.projectionLevels[projId]!
        projectionLevels.forM goLevel
      else
        panic! s!"proj without our metadata: {e} {mdatas}"
      pure $ e.updateProj! (← go b 0)
    | .sort l => do
      goLevel l
      pure e
    | .const _ us =>
      us.forM goLevel
      pure e
    | .lit .. | .mvar .. | .fvar .. =>
      pure e
  goLevel (l : Level) : StateM EraseState Unit :=
    match l with
    | .zero => pure ()
    | .mvar _ => pure ()
    | .succ lp => goLevel lp
    | .max l1 l2 => do
        goLevel l1
        goLevel l2
    | .imax l1 l2 => do
        goLevel l1
        goLevel l2
    | .param n =>
      modify fun s => {s with usedLevels := s.usedLevels.insert n}
  bind (n: Name) (u: Nat) (b: Expr): StateM EraseState (Name × Expr) := do
    modify fun s => {s with usedBVars := s.usedBVars.push false}
    let b <- go b (u - 1)
    let used <- modifyGet fun s => (s.usedBVars.back, {s with usedBVars := s.usedBVars.pop })
    let n := if used || u > 0 then n else Name.anonymous
    pure (n, b)

def unwrap: Expr → Expr
  | .app f _ => unwrap f
  | .lam _ _ b _ => unwrap b
  | .mdata _ e => e
  | e => e

macro "genSubReader" "(" superType:term ")" "(" subType:term ")" fieldName:ident : command => `(
  instance [base: MonadReaderOf $superType M]: MonadReaderOf $subType M where
    read := do pure (← base.read).$fieldName
)

macro "genSubMonad" "(" superType:term ")" "(" subType:term ")" fieldLValue:Lean.Parser.Term.structInstLVal fieldName:ident : command => `(
  instance [base: MonadStateOf $superType M]: MonadStateOf $subType M where
    get := do pure (← base.get).$fieldName
    modifyGet f := do pure (← base.modifyGet (λ σ ↦
      let v := σ.$fieldName
      let σ := {σ with $fieldLValue := default}
      let (r, σ') := f v
      (r, {σ with $fieldLValue := σ'})
    ))
    set σ' := base.modifyGet (λ σ ↦ ((), {σ with $fieldLValue := σ'}))
)

structure Context extends Config, EraseContext, DedupConfig where
  dummyEnv : Environment
  keywords : HashSet String
  implicitKeyword: Name
  binderMDatas: Vector KVMap 4

genSubReader (Context) (EraseContext) toEraseContext
genSubReader (Context) (DedupConfig) toDedupConfig

structure ConstAnalysis where
  numLevels: Nat := 0
  level2idx: HashMap Name (Fin numLevels) := HashMap.empty

  numLevelClauses: Nat := 0
  levelClauses: Vector (OrClause (Fin numLevels)) numLevelClauses

  numSingletonLevelClauses: Nat := 0
  numSingletonLevelClauses_le: numSingletonLevelClauses ≤ numLevelClauses
  singletonLevelClauses: Vector (Option (Fin numSingletonLevelClauses)) numLevels
  --complexLevelClauses: HashMap (OrClause (Fin numLevels)) (Fin numLevelClauses)
  --complexLevelClauses: Array (OrClause (Fin numLevels))
  deriving Repr

instance: Inhabited ConstAnalysis where
  default := {
    levelClauses := Vector.empty,
    numSingletonLevelClauses_le := Nat.le_refl _,
    singletonLevelClauses := Vector.empty
  }

structure GlobalAnalysis where
  consts: HashMap Name ConstAnalysis := {}
  deriving Inhabited

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

def runMetaM'' [MonadReaderOf Context M] [MonadLiftT IO M]
  {α : Type} (env: Environment) (m: MetaM α): M (α × Environment) := do
  let ctx ← pure <| {
    fileName := "<internal>",
    fileMap := FileMap.ofString ""
    options := (← readThe Context).options
    --maxHeartbeats := 200000 * 1000 * 100
  }

  let s := {env}

  let ⟨x, s⟩ ←Core.CoreM.toIO (ctx := ctx) (s := s) do
    Meta.MetaM.run' do
      m

  pure ⟨x, s.env⟩

def runMetaMMod' [MonadReaderOf Context M] [MonadStateOf Environment M] [MonadLiftT IO M]
    {α : Type} (m: MetaM α): M α := do
  let dummyEnv := (← readThe Context).dummyEnv
  let env ← modifyGetThe Environment λ e ↦ (e, dummyEnv)

  let ⟨x, env⟩ ← runMetaM'' env m

  set env
  pure x

def runMetaMMod [MonadReaderOf Context M] [MonadStateOf Environment M] [MonadLiftT IO M]
    (C: Type) (S: Type) [Inhabited S] [MonadReaderOf C M] [MonadStateOf S M]
    {α : Type} (m: (ExceptT MessageData (ReaderT C (StateT S MetaM))) α): M α := do
  let r <- read
  let s ← modifyGet (·, default)

  let ⟨x, s⟩ ←
    runMetaMMod' do
      StateT.run (s := s) do
        ReaderT.run (r := r) do
          ExceptT.run
            m

  set s
  MonadExcept.ofExcept x

def runMetaMRo' [MonadReaderOf Context M] [MonadReaderOf Environment M] [MonadLiftT IO M]
    {α : Type} (m: MetaM α): M α := do
  let env ← readThe Environment
  let ⟨x, _⟩ ← runMetaM'' env m
  pure x

def runMetaMRo [MonadReaderOf Context M] [MonadReaderOf Environment M] [MonadLiftT IO M]
    (C: Type) (S: Type) [Inhabited S] [MonadReaderOf C M] [MonadStateOf S M]
    {α : Type} (m: (ExceptT MessageData (ReaderT C (StateT S MetaM))) α): M α := do
  let r <- read
  let s ← modifyGet (·, default)

  let ⟨x, s⟩ ←
    runMetaMRo' do
      StateT.run (s := s) do
        ReaderT.run (r := r) do
          ExceptT.run
            m

  set s
  MonadExcept.ofExcept x

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

def binderToFin: BinderInfo → Fin 4
| .default => 0
| .implicit => 1
| .strictImplicit => 2
| .instImplicit => 3

def intToBinder: Int → BinderInfo
| 0 => .default
| 1 => .implicit
| 2 => .strictImplicit
| 3 => .instImplicit
| _ => .implicit

def optionIntToBinder: Option Int → BinderInfo
| .none => .default
| .some x => intToBinder x

def levelBinderSeps: String × String := ⟨"{", "}"⟩
def implicitBinderSeps: String × String := ⟨"{", "}"⟩

def binderSeps (always: Bool): BinderInfo → (String × String)
| .default => if always then ("(", ")") else ⟨"", ""⟩
| .implicit | .strictImplicit => implicitBinderSeps
| .instImplicit => ⟨"{{", "}}"⟩

def lotBinderSeps (always: Bool): Option BinderInfo → (String × String)
| .none => levelBinderSeps
| .some x => binderSeps always x

def alwaysBinderSeps := binderSeps true
def maybeBinderSeps := binderSeps false
def alwaysLotBinderSeps := lotBinderSeps true
def maybeLotBinderSeps := lotBinderSeps false

open Lean.Meta in
def annotateApp [MonadReaderOf _root_.Context M] [MonadLiftT MetaM M]
    (e : Expr): M Expr := do
  match e with
  | Expr.app f b => do
    let ft ← inferType f
    let ft ← whnf ft
    if let .forallE _ _ _ bi := ft then
      let f ← annotateApp f
      let e := e.updateApp! f b
      --IO.println s!"-- app: {implicit}: {e} === {ft}"
      if bi != .default then
        let m := (← read).binderMDatas[binderToFin bi]
        pure $ .mdata m e
      else
        pure $ e
    else
      throw m!"unexpected function type {ft}"
  | _ => return e

open Lean.Meta in
def annotateProj [MonadReaderOf _root_.Context M] [MonadStateOf AnnotationData M] [MonadLiftT MetaM M]
    (e : Expr): M Expr := do
  match e with
  | Expr.proj typeName _projIdx structExpr => do
    let structType ← inferType structExpr
    let structType ← whnf structType -- TODO: needed?
    let structType := unwrap structType
    if let .const structTypeName typeLevels := structType then
      if structTypeName != typeName then
        throw m!"structTypeName differs from typeName: {structTypeName} {typeName}"

      let idx <- modifyGet fun st => (st.projectionLevels.size, {st with projectionLevels := st.projectionLevels.push (typeLevels)})
      let m := KVMap.empty.setNat (← read).projectKeyword idx
      pure <| .mdata m e
    else
      throw m!"structType is not a const: {structType}"
      pure  e
  | _ => return e

def annotateExpr [MonadReaderOf Context M] [MonadStateOf AnnotationData M] [MonadLiftT MetaM M] [MonadControlT MetaM M]
  (e : Expr) : M Expr :=
  Meta.transform (m := M) e (post := fun e => do
    match e with
    | Expr.app _ _ => return .done (← annotateApp e)
    | Expr.proj _ _ _ => return .done (← annotateProj e)
    | _ => return .continue
  )

def annotateProjs [MonadReaderOf Context M] [MonadStateOf AnnotationData M] [MonadLiftT MetaM M] [MonadControlT MetaM M]
  (e : Expr) : M Expr :=
  Meta.transform (m := M) e (post := fun e => do
    match e with
    | Expr.proj _ _ _ => return .done (← annotateProj e)
    | _ => return .continue
  )

structure ConstInstance where
  constAnalysis: ConstAnalysis
  levelInstance: LevelInstance constAnalysis.numLevelClauses
  levelParams: Vector Name constAnalysis.numLevels
  deriving Inhabited, Repr

structure BoundLevels where
  --constAnalysis: ConstAnalysis
  --levelInstance: LevelInstance


  -- not necessarily inverse of each other since they may be bound to other letters
  numLevels: Nat
  idx2level: Vector (Option Name) numLevels
  level2level: HashMap Name (Option (Fin numLevels × Name))
  nonzeroComplexClauses: HashSet (OrClause (Fin numLevels))


  --levels: Vector (Option Name) numLevels
  --levelNames: Vector Name numLevels
  --levelNonZero: Vector (Option Bool) numLevels

  deriving Inhabited, Repr

structure ProcessedExpr where
  constInstance: ConstInstance
  erased: ErasedExpr constInstance.constAnalysis.numLevels
  deriving Inhabited
  --levelKinds: Array LevelKind := {}

def processExprAnd [MonadReaderOf Context M] [MonadStateOf Environment M] [MonadLiftT IO M]
    (constInstance: ConstInstance) (levelParams: Vector Name constInstance.constAnalysis.numLevels) (e : DedupedExpr) (keep: Nat) (f: ProcessedExpr → ReaderT AnnotationData (StateT ExprState M) α): M α := do
  let e := e.deduped

  have: MonadStateOf Unit M := unitStateOf
  let (e, annotationData) <- runMetaMRo Context Unit do
    StateT.run (s := ({} : AnnotationData)) do
      annotateExpr e

  -- this must happen last, because it can make the Expr invalid due to erasing lambda types
  let e: ProcessedExpr := {
      constInstance,
      erased := eraseUnused (← readThe EraseContext) annotationData levelParams e keep
    }
  StateT.run' (s := ({} : ExprState)) do
    ReaderT.run (r := annotationData) do
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

def indentOneLevelSpaces := 2

inductive SimpLevel
  | zero : SimpLevel
  | succ : SimpLevel → SimpLevel
  | max : SimpLevel → SimpLevel → SimpLevel
  | param : Name → SimpLevel
  deriving Inhabited, BEq, Ord, Hashable

structure ParamLevel where
  name: Name
  add: Nat
  deriving BEq, Ord

structure NormLevel where
  add: Nat
  maxConst: Nat -- 0 if maxParams is empty
  maxParams: Array ParamLevel -- sorted by name, without duplicate names, if nonempty at least one add is 0

def normalizeSimpLevelRaw (l: SimpLevel): NormLevel :=
  let ⟨maxParams, maxConst⟩ := go ⟨#[], 0⟩  0 l
  let nameEq: ParamLevel → ParamLevel → Bool := λ a b ↦ a.name == b.name
  let maxMerge: ParamLevel → ParamLevel → ParamLevel := λ a b ↦ {name := a.name, add := a.add.max b.add}
  let maxParams := (maxParams.qsort (compare · · |>.isLT)).mergeAdjacentDups (eq := ⟨nameEq⟩) maxMerge
  let add := maxParams.foldl (init := none) λ m x ↦
    match m with
    | .none => some x.2
    | .some m => some <| m.min x.2
  let add := add.getD maxConst
  {
    add,
    maxParams := maxParams.foldl (init := #[]) λ m x ↦
      m.push ⟨x.1, x.2 - add⟩
    maxConst := maxConst - add
  }
where
  go (s: (Array ParamLevel) × Nat) (add: Nat) (l: SimpLevel): (Array ParamLevel) × Nat :=
    match s, l with
    | (a, m), .zero => ⟨a, m.max add⟩
    | (a, m), .param name => ⟨a.push {name, add}, m⟩
    | s, .succ l => go s (add + 1) l
    | s, .max l1 l2 =>
      let s := go s add l1
      let s := go s add l2
      s

def normalizeSimpLevel [MonadReaderOf BoundLevels M]
  (l: SimpLevel): M NormLevel := do
  let n := normalizeSimpLevelRaw l
  let param2add := reverseHashMap n.maxParams (·.name) (n.maxParams[·].add)
  let b ← readThe BoundLevels
  let mut maxConst := n.maxConst

  -- adjust maxConst to reflect knowledge about nonzeroComplexClauses
  for c in b.nonzeroComplexClauses do
    let minAdd := c.foldl (init := none) λ m l => match b.idx2level[l] with
      | .none => panic!("zero level in nonzero clause!")
      | .some n =>
        some <| match param2add.get? n with
        | .none => 0
        | .some a =>
          match m with
          | .none => a + 1
          | .some m => m.min (a + 1)
    match minAdd with
    | .none => ()
    | .some minAdd => maxConst := maxConst.max minAdd

  for n in b.idx2level.toArray do
    match n with
    | .none => ()
    | .some n =>
      match param2add.get? n with
      | .none => ()
      | .some a =>
        maxConst := maxConst.max a

  pure {n with maxConst}

/- all levels known to be zero must have been removed -/
def resolveSimplifiedLevelClause (b: BoundLevels)
    (c: Option (OrClause (Fin b.numLevels))): M Bool := do
  match c with
  | .none => true
  | .some #[] => false
  | .some #[l] =>
    if b.idx2level[l].isSome then
      true
    else
      throw m!"dependent singleton const level clause {l} is supposed to be nonzero, but it's actually zero!"
  | .some c =>
    if b.nonzeroComplexClauses.contains c then
      true
    else
      throw m!"Unable to decide whether dependent const level clause {c.toArray.map (·.val)} is always nonzero or zero: level clause generation is buggy!"

def resolveLevelUnchecked [MonadReaderOf BoundLevels M]
    : Level → M SimpLevel
| .zero => do
  pure .zero
| .succ l => do
  pure <| .succ (← resolveLevelUnchecked l)
| .param n => do
  let boundLevels ← read
  if let .some n := boundLevels.level2level.get? n then
    pure <| match n with
    | .none => .zero
    | .some (_li, n) => .param n
  else
    throw m!"unbound level variable {n}"
| .max l1 l2 => do
  pure <| match ← resolveLevelUnchecked l1, ← resolveLevelUnchecked l2 with
  | s1, .zero => s1
  | .zero, s2 => s2
  | s1, s2 => .max s1 s2
| .imax l1 l2 => do
  match ← resolveLevelUnchecked l2 with
  | .zero => pure .zero
  | s2 =>
    -- here we assume that if we can't prove l2 is zero, it must always be non-zero, due to how we constructed clauses
    pure <| match ← resolveLevelUnchecked l1 with
    | .zero => s2
    | s1 => .max s1 s2
| .mvar _ => throw m!"unexpected mvar in level"

def resolveLevelWithClause (b: BoundLevels)
    (l: Level): M (SimpLevel × Option (OrClause (Fin b.numLevels))) :=
  goBuild b l
where
  goBuild (b: BoundLevels) (l: Level): M (SimpLevel × Option (OrClause (Fin b.numLevels))) := do
    let ⟨s, b⟩ ← StateT.run (s := OrClause.Builder.False?) (m := M) <|
      go b l
    pure ⟨s, OrClause.Builder.build? b⟩
  go (b: BoundLevels)
    (l: Level): StateT (Option (OrClause.Builder (Fin b.numLevels))) M SimpLevel :=
    match l with
    | .zero => do
      pure .zero
    | .succ l => do
      set (OrClause.Builder.True?: Option (OrClause.Builder (Fin b.numLevels)))
      pure <| .succ (← go b l)
    | .param n => do
      if let .some n := b.level2level.get? n then
        match n with
        | .none =>
          pure .zero
        | .some ⟨li, n⟩ =>
          modify (OrClause.Builder.or? · li)
          pure <| .param n
      else
        throw m!"unbound level variable {n}"
    | .max l1 l2 => do
      pure <| match ← go b l1, ← go b l2 with
      | s1, .zero => s1
      | .zero, s2 => s2
      | s1, s2 => .max s1 s2
    | .imax l1 l2 => do
      let ⟨s2, c2⟩ ← goBuild b l2
      match s2 with
      | .zero => pure .zero
      | s2 =>
        modify (OrClause.Builder.orClause?? · c2)
        match c2 with
        | .none => ()
        | .some c2 =>
          if (← resolveSimplifiedLevelClause b c2) == false then
            throw m!"bug: simplified level clause is zero, but SimpLevel is not zero!"
        pure <| match ← go b l1 with
        | .zero => s2
        | s1 => .max s1 s2
    | .mvar _ => throw m!"unexpected mvar in level"

def resolveLevel [MonadReaderOf BoundLevels M]
    (l: Level): M SimpLevel := do
  pure (← resolveLevelWithClause (← readThe BoundLevels) l).1

structure ExprLevels where
  numLevels: Nat
  level2idx: HashMap Name (Fin numLevels)

def collectLevelNonZeroClause (v: ExprLevels) [MonadStateOf (HashSet (OrClause (Fin v.numLevels))) M]
  (c: Option (OrClause (Fin v.numLevels))): M Unit := do
  match c with
  | .some #[] | .none => ()
  | .some c => modify (Std.HashSet.insert · c)

def levelNonZeroClause (v: ExprLevels) [MonadStateOf (HashSet (OrClause (Fin v.numLevels))) M]
    (l: Level): M (Option (OrClause (Fin v.numLevels))) := do
  goBuild l
where
  goBuild (l: Level) := do
    pure <| OrClause.Builder.build? (← go OrClause.Builder.False l)

  go (b: OrClause.Builder (Fin v.numLevels)) (l: Level): M (Option (OrClause.Builder (Fin v.numLevels))) := do
    match l with
    | .zero => some b
    | .succ _ => pure none
    | .param n =>
      match v.level2idx.get? n with
      | .some l => some <| b.or l
      | .none => throw m!"unexpected level parameter {n}"
    | .max l1 l2 =>
      match ← go b l2 with
      | .none => pure none
      | .some b => go b l1
    | .imax _ l2 =>
      let c2 ← goBuild l2
      collectLevelNonZeroClause v c2
      b.orClause? c2
    | .mvar _ => panic! "mvar level"

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

partial def getOrComputeConstAnalysis [MonadStateOf GlobalAnalysis M] [MonadLiftT IO M]
    [MonadReaderOf Environment M] [MonadReaderOf Context M]
    (c: Name): M ConstAnalysis := do
  if let .some sig := (← get).consts.get? c then
    return sig

  let env := ← readThe Environment
  let .some val := env.find? c | throw m!"constant not found: {c}"

  let levels := val.levelParams.toArray
  let numLevels := levels.size
  let level2idx := reverseHashMap levels id id
  let el: ExprLevels := {numLevels, level2idx}

  let r ←
    StateT.run (s := HashSet.empty) (m := M) do
      process el val.type
      if let .some value := val.value? then
        process el value
  let ⟨_, cs⟩ := r
  let cs := cs.toArray
  let singles := HashSet.ofArray <| cs.filterMap (OrClause.single? ·)
  let cs := ((cs.map (OrClause.exclude · singles)).filter (!OrClause.isFalse ·)).sortDedup
  let singles := singles.toArray.sortDedup

  let csLevels := OrClause.union cs
  let (singles, cs) := if cs.size < csLevels.size then
    (singles, cs)
  else
    ((singles ++ csLevels).sortDedup, #[])
  let levelClauses' := singles.map (OrClause.single ·) ++ cs
  let numLevelClauses := levelClauses'.size
  let levelClauses: Vector _ numLevelClauses := ⟨levelClauses', rfl⟩
  let numSingletonLevelClauses := singles.size

  have h: cs.size + numSingletonLevelClauses = numLevelClauses := by
    simp only [numLevelClauses, levelClauses, levelClauses', Array.size_append, Array.size_map]
    rw [Nat.add_comm]
  let numSingletonLevelClauses_le: numSingletonLevelClauses ≤ numLevelClauses := by
    rw [← h]
    apply Nat.le_add_left

  let singletonLevelClauses := reverseVector singles id none (some ·)
  let singletonLevelClauses: Vector (Option (Fin numSingletonLevelClauses)) numLevels :=
    singletonLevelClauses

  --let complexLevelClauses := reverseHashMap cs (·.castAdd singles.size)
  --let complexLevelClauses: HashMap (OrClause (Fin numLevels)) (Fin numLevelClauses) :=
    --h ▸ complexLevelClauses
  --let complexLevelClauses := cs

  let constAnalysis: ConstAnalysis := {numLevels, level2idx, numLevelClauses, levelClauses, numSingletonLevelClauses, numSingletonLevelClauses_le, singletonLevelClauses}
  modify (λ ({consts}: GlobalAnalysis) ↦ {consts := consts.insert c constAnalysis})
  pure constAnalysis
where
  process (el: ExprLevels) (e: Expr): (StateT (HashSet (OrClause (Fin el.numLevels))) M) Unit := do
    let (e, annotationData) <- StateT.run (s := ({} : AnnotationData)) do
      runMetaMRo Context AnnotationData do
        annotateProjs e

    ReaderT.run (r := annotationData) (m := (StateT (HashSet (OrClause (Fin el.numLevels))) M)) do
      goWithMData el [] e

  handleConst (el: ExprLevels) (c: Name) (us: List Level) := do
    let constAnalysis ← getOrComputeConstAnalysis c
    let ucs ← us.toArray.mapM (levelNonZeroClause el)
    let ucs ← toVector ucs constAnalysis.numLevels "number of levels in const usage expression"
    let ccs := constAnalysis.levelClauses.map (OrClause.subst · ucs)
    ccs.toArray.forM (collectLevelNonZeroClause el)

  goWithMData (el: ExprLevels) (ms: List MData) (e: Expr) := do
    let go := goWithMData el []
    match e with
    | .sort u =>
      collectLevelNonZeroClause el (← levelNonZeroClause el u)
    | .const c us =>
      handleConst el c us
    | .proj c _ b => do
      go b
      let projectKeyword := (← readThe Context).projectKeyword
      let projId: Option Nat := ms.findSome? (·.get? projectKeyword)
      if let .some projId := projId then
        let us: List Level := (← readThe AnnotationData).projectionLevels[projId]!
        handleConst el c us
      else
        panic! s!"proj without our metadata: {e} {ms}"
    | .mdata m b => goWithMData el (m :: ms) b
    | .forallE _ d b _ => do go d; go b
    | .lam _ d b _ => do go d; go b
    | .letE _ t v b _  => do go t; go v; go b
    | .app f b => do go f; go b
    | .lit .. | .bvar .. | .fvar .. | .mvar .. => ()
open Std.Format

inductive Precedence
| bottom
| sect
| whereL
| whereR
| inL
| inR
| stmt
| stmtS
| defineL
| defineR
| typingL
| typingR
| parameterizedL
| parameterizedR
| arrowR
| arrowL
| lambdaL
| lambdaR
| lmax
| lmaxS
| appL
| appR
| top
  deriving Inhabited, BEq, Ord, Hashable

instance: LE Precedence := leOfOrd
instance: LT Precedence := ltOfOrd

def tagNoSpaces := 0

/-- State for formatting a pretty string. -/
private structure PrettyState where
  out: String := ""
  column: Nat := 0
  tags: Array Nat := {}
  noSpacesDepth: Nat := 0

instance : MonadPrettyFormat (StateM PrettyState) where
  -- We avoid a structure instance update, and write these functions using pattern matching because of issue #316
  pushOutput s := modify fun ⟨out, col, tags, nsd⟩ =>
    let s := if nsd == 0 then
      s
    else
      s.foldl (fun acc c => if c = ' ' then acc else acc.push c) ""
    ⟨out ++ s, col + s.length, tags, nsd⟩

  pushNewline indent := modify fun ⟨out, _, tags, nsd⟩ =>
    let nl := if out.isEmpty then
      ""
    else
      "\n"
    ⟨out ++ nl.pushn ' ' indent, indent, tags, nsd⟩

  currColumn :=
    return (← get).column

  startTag tag :=
    modify fun ⟨out, col, tags, nsd⟩ =>
      ⟨out, col, tags.push tag, if tag == tagNoSpaces then nsd + 1 else nsd⟩

  endTags n :=
    modify fun st => Nat.rec st (fun _ ⟨out, col, tags, nsd⟩ =>
      let nsd := if tags.back == tagNoSpaces then nsd - 1 else nsd
      ⟨out, col, tags.pop, nsd⟩) n

def myPretty (f : Format) (width : Nat := 150) (indent : Nat := 0) (column := 0) : String :=
  let act : StateM PrettyState Unit := _root_.prettyM f width indent
  PrettyState.out <| act (PrettyState.mk "" column {} 0) |>.snd

--instance : ToString Format where
--  toString _f :=
--    (panic! "called ToString on Format!") ++ "<<<called ToString on Format!>>>"

def lineNoSpace := tag tagNoSpaces line

def nestI := nest indentOneLevelSpaces

def encloseF (o: Format) (f: Format) (c: Format): Format :=
  group (o ++ nestI lineNoSpace) ++ f ++ group (lineNoSpace ++ c)

structure PFormat where
  precedence: Precedence
  format: Format
  deriving Inhabited

def format (format: Format): PFormat :=
  {precedence := .top, format}

def parensGe (precedence: Precedence) (format: Format): PFormat :=
  { precedence, format }

def resolveWithPrec (e: PFormat) (p: Precedence): Format :=
  if p >= e.precedence then
    encloseF "(" e.format ")"
  else
    e.format

def pnil: PFormat :=
  format nil

def token (s: String): PFormat :=
  format $ text s

def enclose (o: Format) (f: PFormat) (c: Format): PFormat :=
  format $ encloseF o (resolveWithPrec f .bottom) c

def encloseWith (s: String × String) (f: PFormat): PFormat :=
  let ⟨o, c⟩ := s
  if o.isEmpty && c.isEmpty then
    f
  else
    enclose (text o) f (text c)

def joinN: List Format → Format
| .nil => .nil
| x :: xs => xs.foldl (·++·) x

def seqGroup (behavior: FlattenBehavior): List Format → Format
| .nil => .nil
| f :: .nil => f
| f :: e :: es => group (f ++ (nest indentOneLevelSpaces (joinN $ (e :: es).map fun e => line ++ e))) behavior

def seqOptNl: List Format → Format
| .nil => .nil
| f :: .nil => f
| f :: e :: es => f ++ (nest indentOneLevelSpaces (joinN $ (e :: es).map fun e => group line ++ e))

def seq2 (a: Format) (b: Format): Format :=
  seqGroup .allOrNone [a, b]


def kwToken (kw: String) (e: String): PFormat :=
  format $ seqGroup .fill [kw, e]

def sect (kw: String) (e: PFormat): PFormat :=
  parensGe .sect $ seqGroup .allOrNone [text kw, (resolveWithPrec e .sect)]

def leftAssoc (left: Precedence) (right: Precedence) (op: Format) (behavior: FlattenBehavior) (f: PFormat) (es: List PFormat): PFormat :=
  if !es.isEmpty then
    let f := resolveWithPrec f left
    let es := es.map fun x => op ++ resolveWithPrec x right
    parensGe right $ seqGroup behavior $ f :: es
  else
    f

def app (f: PFormat) (es: List PFormat): PFormat :=
  leftAssoc .appL .appR "" .allOrNone f es

def parameterized (v: PFormat) (es: List PFormat): PFormat :=
  leftAssoc .parameterizedL .parameterizedR "" .fill v es

def define (v: PFormat) (es: List PFormat): PFormat :=
  leftAssoc .defineL .defineR "= " .fill v es

def andWhere (e: PFormat): PFormat :=
  leftAssoc .whereL .whereR "where" .fill e [token ""]

def rightAssoc (left: Precedence) (right: Precedence) (op: Format) (behavior: FlattenBehavior) (es: List PFormat) (r: PFormat): PFormat :=
  if !es.isEmpty then
    let es := es.map fun x => (resolveWithPrec x left) ++ op
    let r := resolveWithPrec r right
    parensGe left $ seqGroup behavior $ es ++ [r]
  else
    r

def arrow (es: List PFormat) (r: PFormat): PFormat :=
  rightAssoc .arrowL .arrowR " →" .fill es r

def lambdaArrow (es: List PFormat) (r: PFormat): PFormat :=
  let lambda (e: PFormat): PFormat :=
    rightAssoc .lambdaL .lambdaR "λ" .fill [token ""] e

  arrow (es.map (lambda ·)) r

def typing (v: PFormat) (t: PFormat): PFormat :=
  rightAssoc .typingL .typingR " :" .fill [v] t

def inExpr (es: List PFormat) (r: PFormat): PFormat :=
  rightAssoc .inL .inR " in" .fill es r

def infixAssoc (opPrec: Precedence) (opPrecS: Precedence) (op: Format) (es: List PFormat): PFormat :=
  match es with
  | [] => pnil
  | f :: [] => f
  | f :: e :: es =>
    let f := resolveWithPrec f opPrec
    let es := (e :: es).map fun x => op ++ (resolveWithPrec x opPrec)
    parensGe opPrecS $ seqGroup .fill $ f :: es

def stmts (es: List PFormat): PFormat :=
  infixAssoc .stmt .stmtS "; " es

def lmax (es: List PFormat): PFormat :=
  infixAssoc .lmax .lmaxS "⊔ " es

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

def ladd: Nat → PFormat → PFormat
| .zero, e => e
| .succ n, e => app (token "lsuc") [ladd n e]

def lconst: Nat → PFormat
| .zero => token "lzero"
| .succ n => ladd n (token "lone")

def formatLevel [MonadReaderOf Context M]
  (l : NormLevel): M PFormat := do
  match l with
  | {add, maxParams := #[], maxConst} => lconst (add + maxConst)
  | {add, maxParams, maxConst} =>
    let es := if maxConst != 0 then
      #[lconst maxConst]
    else
      #[]
    let es ← pure <| es.append <| ← maxParams.mapM λ x ↦ do pure <| ladd x.add <| ← lparam x.name

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

def bindLevelParamsWith [MonadLiftT IO M]
  {α: Type} (c: ConstAnalysis) (levelParams: Vector Name c.numLevels) (levelParamValues: Vector Name c.numLevels) (levelInstance: LevelInstance c.numLevelClauses) (m: ReaderT BoundLevels M α): M α := do
  let numLevels := c.numLevels

  let idx2level := Fin.foldl c.numLevelClauses (init := Vector.ofFn λ i ↦ some levelParams[i]) λ v i ↦
    if levelInstance[i] = false then
      c.levelClauses[i].foldl (init := v) λ v l ↦ v.set l none
    else
      v

  let level2level := reverseHashMap levelParamValues.toArray id (λ i ↦
    have h := by
      apply Fin.val_lt_of_le
      simp only [Vector.size_eq, numLevels, Nat.le_refl]
    have h': levelParamValues.toArray.size = numLevels := by
      exact levelParamValues.size_eq
    (idx2level[i]'h).map (λ l ↦ ⟨h' ▸ i, l⟩)
  )

  let nonzeroComplexClauses := Fin.foldl (c.numLevelClauses - c.numSingletonLevelClauses) (init := Std.HashSet.empty) λ s i ↦
    let i' := i.addNat c.numSingletonLevelClauses
    let h := by
      apply Fin.val_lt_of_le
      simp only [c.numSingletonLevelClauses_le, Nat.sub_add_cancel, Nat.le_refl]
    let cl := c.levelClauses[i']'h
    s.insert <| cl.filter (idx2level[·].isSome)

  --nonzeroComplexClauses: HashSet (OrClause (Fin numLevels))

  let r: BoundLevels := {numLevels, idx2level, level2level, nonzeroComplexClauses}
  --traceComment s!"BoundLevels: {repr r}"
  ReaderT.run (r := r) do
    m

namespace ProcessedExpr
def numLevels (e: ProcessedExpr) := e.constInstance.constAnalysis.numLevels

-- TODO: probably move into processExprAnd
def bindLevelParams [MonadLiftT IO M]
  {α: Type} (e: ProcessedExpr) (m: ReaderT BoundLevels M α): M α := do
  let ci := e.constInstance
  bindLevelParamsWith ci.constAnalysis ci.levelParams e.erased.levelParams ci.levelInstance m
end ProcessedExpr

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
  let ucs ← us.mapM (resolveLevelWithClause boundLevels)
  let ucs ← toVector ucs constAnalysis.numLevels "levels in const usage expression"
  let ccs := constAnalysis.levelClauses.map (OrClause.subst · (ucs.map (·.2)))
  let levelInstance ← ccs.mapM (resolveSimplifiedLevelClause boundLevels)
  let ucs := specializeLevelParams constAnalysis levelInstance ucs

  addDependency n levelInstance.toArray

  let c := token (f (← stringifyGlobalName n levelInstance))

  if withLevels && !us.isEmpty then
    let levels: List PFormat ← (← ucs.mapM <| fun (s, _c) => do pure <| encloseWith levelBinderSeps (← formatLevel (normalizeSimpLevel s))).toList
    app c levels
  else
    c

-- must be inside bindLevelParams and bind for outer params
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
    | .sort l => match normalizeSimpLevel (← resolveLevel l) with
      | l@{add := n, maxParams := #[], maxConst := 0} =>
        match n with
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
      | {add := .succ addp, maxParams, maxConst} =>
        app (token "Type") [← formatLevel {add := addp, maxParams, maxConst}]
      | l =>
        app (token "Set") [← formatLevel l]
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
    [Inhabited α] (e: ProcessedExpr) (n: Nat) (strict: Bool) (f: List Name → List MData → Expr → ReaderT BoundLevels M α): M ((Array ((Option BinderInfo) × String × PFormat)) × α) := do
  e.bindLevelParams do
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
  e.bindLevelParams do
    formatParamsAndHandleExpr e n true (formatExprInnerWithLevelParams · · ·)

def formatArgsAndHandleExpr
    (e: ProcessedExpr) (f: List MData → Expr → Nat → ReaderT BoundLevels M ((Array ((Option BinderInfo) × String)) × PFormat)): M ((Array ((Option BinderInfo) × String)) × PFormat) := do
  e.bindLevelParams do
    let levelParams := specializeLevelParams e.constInstance.constAnalysis e.constInstance.levelInstance e.erased.levelParams
    let (a, b) <- goLevels levelParams.toList e.erased.expr
    pure (a.reverse, b)
where
  goLevels (levels: List Name) (e: Expr) : ReaderT BoundLevels M ((Array ((Option BinderInfo) × String)) × PFormat) :=
    match levels with
    | n :: levels => do
      let (n, (a, b)) <- bindIf true n (goLevels levels e)
      pure (a.push (none, n), b)
    | [] => goExpr [] e 0

  goExpr (mdatas: List MData) (e: Expr) (depth: Nat): ReaderT BoundLevels M ((Array ((Option BinderInfo) × String)) × PFormat) := do
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
        e.bindLevelParams do
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
          e.bindLevelParams do
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
      e.bindLevelParams do
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
          let ctorConst ← e.bindLevelParams do
            formatConst ctor.name (ctorLevelParams.toArray.map (.param ·)) id false
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

def translateConstant'
  (c : Name) (levelInstance: GenLevelInstance): M (Option (TranslateOutput M)) := do
  if (← getThe Visited).visitedConstants.contains (c, levelInstance) then
    return none
  modifyThe Visited fun st => { st with visitedConstants := st.visitedConstants.insert (c, levelInstance) }

  try
    pure <| some <| ← translate c
  catch e =>
    throw m!"translating constant {c}\n{e}"
where
  translate (c: Name):= do
    let env := ← getThe Environment
    let .some val := env.find? c | throw m!"not found"

    let constAnalysis ← getOrComputeConstAnalysis c
    let levelInstance ← toVector levelInstance constAnalysis.numLevelClauses "level kinds in level instance for constant to be translated"
    let levelParams ← toVector val.levelParams.toArray constAnalysis.numLevels "level parameters in constant declaration compared to analysis"
    let (ns, n) ← declarationName c levelInstance

    let constInstance: ConstInstance := {constAnalysis, levelInstance, levelParams}
    --comment s!"const instance for {c}: {repr constInstance}"

    match val with
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
      pure default
    | .recInfo val =>
      translateRecursor c constInstance ns n val

variable (M) in
inductive QueueItem
| const (c: Name) (levelInstance: GenLevelInstance)
| out (m: M Unit)

partial def translateConstantQueue (a: Array (QueueItem M)): M Unit := do
  let item := a.back?
  match item, a.pop with
  | .none, _ => ()
  | .some (.const c levelInstance), a =>
    translateConstantQueue <| match ← translateConstant' c levelInstance with
    | .some (deps, out) =>
      let depsItems := deps.map fun (n, levelInstance) => .const n levelInstance
      (a.push (.out out)).append depsItems.reverse
    | .none => a
  | .some (.out m), a =>
    m
    translateConstantQueue a

def translateConstant
  (c : Name) (levelInstance: GenLevelInstance): M Unit := do
  translateConstantQueue #[.const c levelInstance]

def translateConstantVariants
  (c : Name): M Unit := do
  let constAnalysis ← getOrComputeConstAnalysis c
  StateT.run' (s := #[]) do
    go constAnalysis.numLevelClauses
where
  go (n: Nat): StateT GenLevelInstance M Unit := do
    match n with
    | .zero => translateConstant c (← getThe GenLevelInstance)
    | .succ n =>
      #[false, true].forM fun sk => do
        modifyThe GenLevelInstance (·.push sk)
        go n
        modifyThe GenLevelInstance (·.pop)

end Translate
