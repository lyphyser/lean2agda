import Batteries.Data.Vector.Basic
import Std.Data.HashSet.Basic

open Batteries (Vector)

abbrev LevelInstance (n: Nat) := Vector Bool n

abbrev GenLevelInstance := Array Bool
