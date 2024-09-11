import Lean2Agda.Data.OrClause
import Batteries.Data.Vector.Basic

open Batteries (Vector)

structure MaxLevel (numLevels: Nat) where
  const: Nat
  params: Vector (Option Nat) numLevels

structure NormLevel (numLevels: Nat) where
  add: Nat
  max: MaxLevel numLevels

namespace MaxLevel
def maxParam {numLevels: Nat} (m: MaxLevel numLevels) (add: Nat) (l: Fin numLevels): MaxLevel numLevels :=
  let {const, params} := m
  let add := match params[l] with
  | .none => add
  | .some n => n.max add
  {const, params := params.set l add}

def maxConst {numLevels: Nat} (m: MaxLevel numLevels)  (add: Nat): MaxLevel numLevels :=
  let {const, params} := m
  {const := const.max add, params}

def maxMaxLevel {numLevels: Nat} (m: MaxLevel numLevels) (add: Nat) (ml: MaxLevel numLevels): MaxLevel numLevels :=
  let {const, params} := m
  let {const := bconst, params := bparams} := ml
  let params := Fin.foldl numLevels (init := params) λ params i ↦
    let v := match params[i], bparams[i] with
    | .none, .none => none
    | .some a, .none => some a
    | .none, .some b => some (add + b)
    | .some a, .some b => some <| a.max (add + b)
    params.set i v
  let const := const.max (add + bconst)

  {const, params}

def toClause {numLevels: Nat} (nl: MaxLevel numLevels): Option (OrClause (Fin numLevels)) :=
  let {const, params} := nl
  if const = 0 then
    let b := Fin.foldl numLevels (init := OrClause.Builder.False?) λ b i ↦
      match params[i] with
      | .none => b
      | .some add =>
        if add = 0 then
          OrClause.Builder.or? b i
        else
          OrClause.Builder.True?
    OrClause.Builder.build? b
  else
    OrClause.True?

def normalize {numLevels: Nat} (ml: MaxLevel numLevels): NormLevel numLevels :=
  let {params, const} := ml
  let minMaxParam := params.toArray.foldl (init := none) λ m x ↦
    match x with
    | .none => m
    | .some x =>
      match m with
      | .none => some (x, x)
      | .some (minParam, maxParam) => some (minParam.min x, maxParam.max x)

  match minMaxParam with
  | .some (add, maxParam) =>
    {
      add,
      max := {
        params := params.map (·.map (· - add))
        const := if const > maxParam then const - add else 0
      }
    }
  | .none =>
    {
      add := const,
      max := {params, const := 0}
    }
end MaxLevel

namespace NormLevel
def toClause {numLevels: Nat} (nl: NormLevel numLevels): Option (OrClause (Fin numLevels)) :=
  let {add, max} := nl
  if add = 0 then
    max.toClause
  else
    OrClause.True?
end NormLevel
