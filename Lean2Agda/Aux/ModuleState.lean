import Lean2Agda.Data.Value
import Lean2Agda.Data.Monad
import Lean2Agda.Data.ExtraBatteries
import Lean2Agda.Output.PFormat
import Lean2Agda.Output.Pretty

open Lean (Format)

structure ModuleState where
  curNamespace: Array String := {}
  indentSpace: Nat := 0
  output: IO.FS.Stream
  deriving Inhabited

def myPretty (f : Format) (width : Nat := 150) (indent : Nat := 0) (column := 0) : String :=
  let act : StateM PrettyState Unit := _root_.prettyM f width indent
  PrettyState.out <| act (PrettyState.mk "" column {} 0) |>.snd

section
local macro "M": term => `(IO)
variable [Value ModuleState]

open Std.Format in
def outputIndented
  (levels: Nat) (f: PFormat): M Unit := do
  let self := valueOf ModuleState
  self.output.putStr <| (myPretty <| nest (self.indentSpace + levels * indentOneLevelSpaces) <| (text "\n") ++ (resolveWithPrec f .bottom)) ++ "\n"

def output
  (f: PFormat): M Unit := do
  outputIndented 0 f

def println
  (s: String) (pfx: String := ""): M Unit := do
  --output (format (text s))
  let self := valueOf ModuleState
  self.output.putStr s!"{pfx.pushn ' ' $ self.indentSpace}{s}\n"

def nlprintln
  (s: String): M Unit := do
  println s (pfx := "\n")

def comment
  (s: String): M Unit := do
  nlprintln ("--" ++ (s.replace "\n" "\n--"))

def outputModulePrelude: M Unit := do
  println "{-# OPTIONS --prop --type-in-type #-}"
  println "open Agda.Primitive" -- TODO: fix this since it could conflict with Lean
  println ""
  println "Type : (u : Level) → Set (lsuc (lsuc u))"
  println "Type u = Set (lsuc u)"
  println ""
  println "lone : Level"
  println "lone = lsuc lzero"
end

def useBrokenNamespaceModules := false

local macro "M": term => `(StateT ModuleState IO)

def goToNamespace
  (a : Array String) : M Unit := do
  if useBrokenNamespaceModules then
    let p := commonPrefixLength (← get).curNamespace a
    modify fun s => {s with curNamespace := s.curNamespace.extract 0 p, indentSpace := p * indentOneLevelSpaces}
    (a.extract p a.size).forM openModule
where openModule (m: String): M Unit := do
  have := ← getValue
  nlprintln s!"module {m} where"
  modify fun s => {s with curNamespace := s.curNamespace.push m, indentSpace := indentOneLevelSpaces}
