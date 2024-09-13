import Lean2Agda.Data.OrClause
import Lean2Agda.Data.MaxLevel
import Lean2Agda.Aux.ConstInstance

import Batteries.Data.Vector.Basic
import Std.Data.HashMap.Basic

open Batteries (Vector)
open Lean (Expr MData Level MessageData Name Environment)
open Std (HashMap)

local macro "M": term => `(Except MessageData)

structure BoundLevels where
  constInstance: ConstInstance
  input2idx: HashMap Name (Fin constInstance.constAnalysis.numLevels)

  deriving Inhabited, Repr

namespace BoundLevels
abbrev numLevels (b: BoundLevels) := b.constInstance.constAnalysis.numLevels

def isAlwaysZero (b: BoundLevels) (l: Fin b.numLevels): Bool :=
  b.constInstance.idx2output[l].isNone
end BoundLevels

/- resolveLevel and applyNonZeroClauses actually do all the work -/
def resolveSimplifiedLevelClause (ci: ConstInstance)
    (c: Option (OrClause (Fin ci.numLevels))): M Bool := do
  match c with
  | .none => pure true
  | .some #[] => pure false
  | .some c =>
    throw m!"Unable to decide whether dependent const level clause {c.toArray.map (·.val)} is always nonzero or zero: level clause generation or level resolution is buggy!"

/- apply the fact that e.g. if we know that u OR v != 0, then max(u + 3, v + 6, ...) >= 4, so rewrite the const in the max accordingly -/
private def applyNonZeroClauses
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
  pure <| MaxLevel.normalize <| ← goBuild l
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

def boundLevels
  (ci: ConstInstance) (levelParamValues: Vector Name ci.numLevels): BoundLevels :=

  let h: levelParamValues.toArray.size = ci.constAnalysis.numLevels := by
    exact levelParamValues.size_eq
  let input2idx := h ▸ reverseHashMap levelParamValues.toArray id id

  {constInstance := ci, input2idx}
