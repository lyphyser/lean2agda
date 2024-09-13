import Lean2Agda

import Lean.Util.Path
import Lean.Environment

structure Options extends Config where
  imports: List String := []
  constants: List String := []

def parseOptions (o: Options) (args: List String): Options :=
  match args with
  | "--erase-lambda-types" :: rest =>
    parseOptions { o with eraseLambdaTypes := true } rest
  | "--omit-implicits" :: rest =>
    parseOptions { o with omitImplicits := true } rest
  | _ =>
    let (imports, constants) := args.span (· != "--")
    { o with imports, constants }

open Lean in
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let options := parseOptions {} args

  let imports := options.imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
  let env ← importModules imports {}
  let constants := match options.constants.tail? with
    | some cs => cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
    | none    => env.constants.toList.map Prod.fst |>.filter (!·.isInternal)

  TranslateM.run options.toConfig env do
    for c in constants do
      let _ ← translateConstantVariants c
