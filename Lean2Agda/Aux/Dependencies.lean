import Lean2Agda.Data.LevelInstance

import Std.Data.HashSet.Basic

open Lean (Name)
open Std (HashSet)

structure Dependencies where
  dependencies: HashSet (Name × GenLevelInstance) := {}
  deriving Inhabited

variable {M} [Monad M]
  [MonadStateOf Dependencies M]

def addDependency
  (n: Name) (levelInstance: GenLevelInstance): M Unit := do
  modify fun st => { st with dependencies := st.dependencies.insert (n, levelInstance)}
