import Lean2Agda.Passes.Annotate

import Std.Data.HashSet.Basic
import Lean.Expr
import Batteries.Data.Vector.Basic

open Batteries (Vector)
open Lean hiding HashSet HashMap
open Std (HashSet)

structure EraseConfig where
  eraseLambdaTypes: Bool := false
  omitImplicits: Bool := false

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
