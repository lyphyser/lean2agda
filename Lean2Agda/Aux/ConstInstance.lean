import Lean2Agda.Analysis.ConstAnalysis
import Lean2Agda.Data.OrClause
import Lean2Agda.Data.LevelInstance
import Batteries.Data.Vector.Basic

open Batteries (Vector)
open Lean (Name)

structure ConstInstance where
  constAnalysis: ConstAnalysis
  levelInstance: LevelInstance constAnalysis.numLevelClauses
  levelParams: Vector Name constAnalysis.numLevels
  idx2output: Vector (Option Name) constAnalysis.numLevels
  nonzeroClauses: Array (OrClause (Fin constAnalysis.numLevels))
  deriving Inhabited, Repr

namespace ConstInstance
abbrev numLevels (ci: ConstInstance) := ci.constAnalysis.numLevels

def numSpecializedLevelParams (ci: ConstInstance): Nat :=
  _root_.numSpecializedLevelParams ci.constAnalysis ci.levelInstance
end ConstInstance


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
