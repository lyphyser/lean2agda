import Lean2Agda.Data.Value
import Lean2Agda.Data.OrClause
import Lean2Agda.Data.LevelInstance
import Lean2Agda.Data.ExtraBatteries
import Lean2Agda.Passes.Annotate
import Lean2Agda.Lean.RunMetaM

import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Batteries.Data.Vector.Basic
import Lean.Expr

open Batteries (Vector)
open Lean (Name Expr MData Environment Level)
open Std (HashMap HashSet)

variable {M : Type → Type} [Monad M] [MonadExceptOf Lean.MessageData M]

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

private def collectLevelNonZeroClause (v: ExprLevels) [MonadStateOf (HashSet (OrClause (Fin v.numLevels))) M]
  (c: Option (OrClause (Fin v.numLevels))): M Unit := do
  match c with
  | .some #[] | .none => pure ()
  | .some c => modify (Std.HashSet.insert · c)

private def levelNonZeroClause (v: ExprLevels) [MonadStateOf (HashSet (OrClause (Fin v.numLevels))) M]
    (l: Level): M (Option (OrClause (Fin v.numLevels))) := do
  goBuild l
where
  goBuild (l: Level) := do
    pure <| OrClause.Builder.build? (← go OrClause.Builder.False l)

  go (b: OrClause.Builder (Fin v.numLevels)) (l: Level): M (Option (OrClause.Builder (Fin v.numLevels))) := do
    match l with
    | .zero => pure <| some b
    | .succ _ => pure none
    | .param n =>
      match v.level2idx.get? n with
      | .some l => pure <| some <| b.or l
      | .none => throw ↑s!"unexpected level parameter {n}"
    | .max l1 l2 =>
      match ← go b l2 with
      | .none => pure none
      | .some b => go b l1
    | .imax _ l2 =>
      let c2 ← goBuild l2
      collectLevelNonZeroClause v c2
      pure <| b.orClause? c2
    | .mvar _ => panic! "mvar level"

partial def getOrComputeConstAnalysis [MonadStateOf GlobalAnalysis M] [MonadLiftT IO M]
    [Value Environment] [Value AnnotateContext] [Value MetaMContext]
    (c: Name): M ConstAnalysis := do
  if let .some sig := (← get).consts.get? c then
    return sig

  let env := valueOf Environment
  let .some val := env.find? c | throw ↑s!"constant not found: {c}"

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
      runMetaMRo AnnotationData do
        annotateProjs (ε := Lean.MessageData) e

    have := mkValue annotationData
    goWithMData el [] e

  handleConst (el: ExprLevels) (c: Name) (us: List Level) := do
    let constAnalysis ← getOrComputeConstAnalysis c
    let ucs ← us.toArray.mapM (levelNonZeroClause el)
    let ucs ← toVector ucs constAnalysis.numLevels "number of levels in const usage expression"
    let ccs := constAnalysis.levelClauses.map (OrClause.subst · ucs)
    ccs.toArray.forM (collectLevelNonZeroClause el)

  goWithMData (el: ExprLevels) [Value AnnotationData] (ms: List MData) (e: Expr) := do
    let go := goWithMData el []
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
    | .mdata m b => goWithMData el (m :: ms) b
    | .forallE _ d b _ => do go d; go b
    | .lam _ d b _ => do go d; go b
    | .letE _ t v b _  => do go t; go v; go b
    | .app f b => do go f; go b
    | .lit .. | .bvar .. | .fvar .. | .mvar .. => pure ()
