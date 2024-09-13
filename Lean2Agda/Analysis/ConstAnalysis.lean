import Lean2Agda.Data.Value
import Lean2Agda.Data.Monad
import Lean2Agda.Data.OrClause
import Lean2Agda.Data.LevelInstance
import Lean2Agda.Data.ExtraBatteries
import Lean2Agda.Passes.Annotate
import Lean2Agda.Lean.RunMetaM

import Lake.Util.EStateT
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Batteries.Data.Vector.Basic
import Lean.Expr

open Lake (EStateT)
open Batteries (Vector)
open Lean (ConstantInfo Name Expr MData MessageData Environment Level)
open Std (HashMap HashSet)

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

instance: Inhabited ConstAnalysis where
  default := {
    levelClauses := Vector.empty,
    numSingletonLevelClauses_le := Nat.le_refl _,
    singletonLevelClauses := Vector.empty
  }

structure GlobalAnalysis where
  consts: HashMap Name ConstAnalysis := {}
  deriving Inhabited

private structure ExprLevels where
  numLevels: Nat
  level2idx: HashMap Name (Fin numLevels)

section
variable (el: ExprLevels)
local macro "M": term => `(EStateM MessageData (HashSet (OrClause (Fin el.numLevels))))

private def collectLevelNonZeroClause
  (c: Option (OrClause (Fin el.numLevels))): M Unit := do
  match c with
  | .some #[] | .none => pure ()
  | .some c => modify (Std.HashSet.insert · c)

private def levelNonZeroClause
    (l: Level): M (Option (OrClause (Fin el.numLevels))) := do
  goBuild l
where
  goBuild (l: Level) := do
    pure <| OrClause.Builder.build? (← go OrClause.Builder.False l)

  go (b: OrClause.Builder (Fin el.numLevels)) (l: Level): M (Option (OrClause.Builder (Fin el.numLevels))) := do
    match l with
    | .zero => pure <| some b
    | .succ _ => pure none
    | .param n =>
      match el.level2idx.get? n with
      | .some l => pure <| some <| b.or l
      | .none => throw m!"unexpected level parameter {n}"
    | .max l1 l2 =>
      match ← go b l2 with
      | .none => pure none
      | .some b => go b l1
    | .imax _ l2 =>
      let c2 ← goBuild l2
      collectLevelNonZeroClause el c2
      pure <| b.orClause? c2
    | .mvar _ => panic! "mvar level"
end

section
variable [Value GlobalAnalysis] [Value MetaMContext] [Value Environment] [Value AnnotateContext]

section
variable
  (el: ExprLevels)

local macro "M": term => `(EStateT MessageData (HashSet (OrClause (Fin el.numLevels))) IO)

def getComputedConstAnalysis (c: Name): ConstAnalysis :=
  (valueOf GlobalAnalysis).consts.get! c

private def handleConst (c: Name) (us: List Level) := do
  let constAnalysis := getComputedConstAnalysis c
  let ucs ← us.toArray.mapM (levelNonZeroClause el)
  let ucs ← toVector ucs constAnalysis.numLevels "number of levels in const usage expression"
  let ccs := constAnalysis.levelClauses.map (OrClause.subst · ucs)
  ccs.toArray.forM (collectLevelNonZeroClause el)

private def process (e: Expr): M Unit := do
  let (e, annotationData) <- StateT.run (s := ({} : AnnotationData)) do
    runMetaMRo AnnotationData do
      annotateProjs e

  have := mkValue annotationData
  go e
where
  go [Value AnnotationData] (e: Expr) := goWithMData [] e

  goWithMData [Value AnnotationData] (ms: List MData) (e: Expr) := do
    match e with
    | .sort u =>
      collectLevelNonZeroClause el (← levelNonZeroClause el u)
    | .const c us =>
      handleConst el c us
    | .proj c _ b => do
      go b
      let projectKeyword := (valueOf AnnotateContext).projectKeyword
      let projId: Option Nat := ms.findSome? (·.get? projectKeyword)
      if let .some projId := projId then
        let us: List Level := (valueOf AnnotationData).projectionLevels[projId]!
        handleConst el c us
      else
        panic! s!"proj without our metadata: {e} {ms}"
    | .mdata m b => goWithMData (m :: ms) b
    | .forallE _ d b _ => do go d; go b
    | .lam _ d b _ => do go d; go b
    | .letE _ t v b _  => do go t; go v; go b
    | .app f b => do go f; go b
    | .lit .. | .bvar .. | .fvar .. | .mvar .. => pure ()

end

local macro "M": term => `(ExceptT MessageData IO)

private def computeConstAnalysis
    [Value GlobalAnalysis] [Value Environment] [Value AnnotateContext] [Value MetaMContext]
    (val: ConstantInfo): M ConstAnalysis := do
  let levels := val.levelParams.toArray
  let numLevels := levels.size
  let level2idx := reverseHashMap levels id id
  let el: ExprLevels := {numLevels, level2idx}

  let r: IO (Except _ _ × _) := Lake.EResult.toProd <$> EStateT.run (init := HashSet.empty) do
    process el val.type
    if let .some value := val.value? then
      process el value
  let ⟨e, cs⟩ ← r
  e
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

  pure <| {numLevels, level2idx, numLevelClauses, levelClauses, numSingletonLevelClauses, numSingletonLevelClauses_le, singletonLevelClauses}

end

private inductive QueueItem
| this (c: Name) (val: ConstantInfo)
| withDeps (c: Name)

partial def getOrComputeConstAnalysis
    [Value Environment] [Value AnnotateContext] [Value MetaMContext]
    (c: Name): EStateT MessageData GlobalAnalysis IO ConstAnalysis :=
  go #[] (.withDeps c)
where
  go' (q: Array QueueItem) (constAnalysis: ConstAnalysis) :=
    match q.backPop? with
    | .none => pure constAnalysis
    | .some (item, q) => go q item

  go (q: Array QueueItem) (item: QueueItem) := do
    match item with
    | .withDeps c => do
      if let .some constAnalysis := (← get).consts.get? c then
        go' q constAnalysis
      else
        let env := valueOf Environment
        let .some val := env.find? c | throw m!"constant not found: {c}"

        let a := val.type.getUsedConstants
        let a := if let .some value := val.value? then
          value.foldConsts a fun c cs => cs.push c
        else
          a
        let a := a.sortDedup.reverse.map (.withDeps ·)
        match a.backPop? with
        | .some (item, a) =>
          let q := q.push (.this c val)
          let q := q.append a
          go q item
        | .none =>
          go q (.this c val)
    | .this c val =>
      let constAnalysis ← (
        have := ← getTheValue GlobalAnalysis
        computeConstAnalysis val
      )
      modify (λ ({consts}: GlobalAnalysis) ↦ {consts := consts.insert c constAnalysis})
      go' q constAnalysis
