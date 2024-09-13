import Lean2Agda.Data.Value
import Lean2Agda.Data.Monad
import Lean2Agda.Data.LevelInstance
import Lean2Agda.Aux.HygienicNames
import Lean2Agda.Aux.Ident
import Lean2Agda.Passes.Dedup

import Std.Data.HashMap.Basic
import Batteries.Data.Vector.Basic

open Batteries (Vector)
open Std (HashMap)
open Lean (Name MessageData)

def usebrokenNamespaceModules := false
def dot := if usebrokenNamespaceModules then '.' else ':'
def intPrefix := if usebrokenNamespaceModules then "$" else ""

structure GlobalNames where
  hygienicNames: HygienicNames := {}
  nameReplacements: HashMap Name String := {}
  deriving Inhabited

variable [Value Language] [Value DedupData]
local macro "M": term => `(EStateM MessageData GlobalNames)

def stringifyUnqualifiedName
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
    pure <| stringifyIdent s
where
  toName (p: Name) (n: Name) (suffix: String): M String := do
    if n == p then
      throw m!"qualified name is equal to namespace: {n}"
    else
      match n with
      | .anonymous => throw m!"qualified name is not in expected namespace"
      | .str v "_@" =>
        let v := s!"{v}"
        let hn := makeHygienicName v
        modifyGetThe GlobalNames λ {hygienicNames, nameReplacements} ↦
          let (r, hygienicNames) := hn.permanentFn hygienicNames
          (r, {hygienicNames, nameReplacements := nameReplacements.insert name r})
      | .str n s =>
        let s ← if dot == '.' then
          pure <| stringifyIdent s
        else
          pure s
        toNameDot p n s!"{s}{suffix}"
      | .num n i =>
        if n == (valueOf DedupData).dedupPrefix then
          pure s!"#{i}"
        else
          toNameDot p n s!"{intPrefix}{i}{suffix}"
  toNameDot (p: Name) (n: Name) (suffix: String): M String :=
    if n == p then
      pure suffix
    else
      toName p n s!"{dot}{suffix}"

def stringifyGlobalName
  (n : Name) {numLevelClauses: Nat} (levelInstance: LevelInstance numLevelClauses): M String :=
  match n with
  | .anonymous => throw m!"anonymous global name"
  | _ => stringifyUnqualifiedName Name.anonymous n levelInstance

private def nameToArray
  (n : Name) : M (Array String) := do
  pure (← go n Array.empty).reverse
where go (n: Name) (a: Array String): M (Array String) := do
  match n with
  | .anonymous => pure a
  | .str n s => go n (a.push (stringifyIdent s))
  | .num n i => go n (a.push s!"{intPrefix}{i}")

def declarationName
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
