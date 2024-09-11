import Lake
open Lake DSL

package lean2agda

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

lean_lib Lean2Agda

@[default_target]
lean_exe lean2agda where
  root := `Main
  supportInterpreter := true
