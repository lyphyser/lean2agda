import Batteries.Data.Vector.Basic
import Std.Data.HashSet.Basic

open Batteries (Vector)
open Std (HashMap HashSet)

abbrev OrClause (α) := Array α

namespace OrClause
def False: OrClause α := #[]
def True?: Option (OrClause α) := none
def False?: Option (OrClause α) := some False

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
