import Lean.Expr
import Init.Data.Format.Basic

open Std (Format)
open Std.Format

def indentOneLevelSpaces := 2

inductive Precedence
| bottom
| sect
| whereL
| whereR
| inL
| inR
| stmt
| stmtS
| defineL
| defineR
| typingL
| typingR
| parameterizedL
| parameterizedR
| arrowR
| arrowL
| lambdaL
| lambdaR
| lmax
| lmaxS
| appL
| appR
| top
  deriving Inhabited, BEq, Ord, Hashable

instance: LE Precedence := leOfOrd
instance: LT Precedence := ltOfOrd

def tagNoSpaces := 0

/-- State for formatting a pretty string. -/
structure PrettyState where
  out: String := ""
  column: Nat := 0
  tags: Array Nat := {}
  noSpacesDepth: Nat := 0

instance : MonadPrettyFormat (StateM PrettyState) where
  -- We avoid a structure instance update, and write these functions using pattern matching because of issue #316
  pushOutput s := modify fun ⟨out, col, tags, nsd⟩ =>
    let s := if nsd == 0 then
      s
    else
      s.foldl (fun acc c => if c = ' ' then acc else acc.push c) ""
    ⟨out ++ s, col + s.length, tags, nsd⟩

  pushNewline indent := modify fun ⟨out, _, tags, nsd⟩ =>
    let nl := if out.isEmpty then
      ""
    else
      "\n"
    ⟨out ++ nl.pushn ' ' indent, indent, tags, nsd⟩

  currColumn :=
    return (← get).column

  startTag tag :=
    modify fun ⟨out, col, tags, nsd⟩ =>
      ⟨out, col, tags.push tag, if tag == tagNoSpaces then nsd + 1 else nsd⟩

  endTags n :=
    modify fun st => Nat.rec st (fun _ ⟨out, col, tags, nsd⟩ =>
      let nsd := if tags.back == tagNoSpaces then nsd - 1 else nsd
      ⟨out, col, tags.pop, nsd⟩) n

--instance : ToString Format where
--  toString _f :=
--    (panic! "called ToString on Format!") ++ "<<<called ToString on Format!>>>"

def lineNoSpace := tag tagNoSpaces line

def nestI := nest indentOneLevelSpaces

def encloseF (o: Format) (f: Format) (c: Format): Format :=
  group (o ++ nestI lineNoSpace) ++ f ++ group (lineNoSpace ++ c)

structure PFormat where
  precedence: Precedence
  format: Format
  deriving Inhabited

def format (format: Format): PFormat :=
  {precedence := .top, format}

def parensGe (precedence: Precedence) (format: Format): PFormat :=
  { precedence, format }

def resolveWithPrec (e: PFormat) (p: Precedence): Format :=
  if p >= e.precedence then
    encloseF "(" e.format ")"
  else
    e.format

def pnil: PFormat :=
  format nil

def token (s: String): PFormat :=
  format $ text s

def enclose (o: Format) (f: PFormat) (c: Format): PFormat :=
  format $ encloseF o (resolveWithPrec f .bottom) c

def encloseWith (s: String × String) (f: PFormat): PFormat :=
  let ⟨o, c⟩ := s
  if o.isEmpty && c.isEmpty then
    f
  else
    enclose (text o) f (text c)

def joinN: List Format → Format
| .nil => .nil
| x :: xs => xs.foldl (·++·) x

def seqGroup (behavior: FlattenBehavior): List Format → Format
| .nil => .nil
| f :: .nil => f
| f :: e :: es => group (f ++ (nest indentOneLevelSpaces (joinN $ (e :: es).map fun e => line ++ e))) behavior

def seqOptNl: List Format → Format
| .nil => .nil
| f :: .nil => f
| f :: e :: es => f ++ (nest indentOneLevelSpaces (joinN $ (e :: es).map fun e => group line ++ e))

def seq2 (a: Format) (b: Format): Format :=
  seqGroup .allOrNone [a, b]


def kwToken (kw: String) (e: String): PFormat :=
  format $ seqGroup .fill [kw, e]

def sect (kw: String) (e: PFormat): PFormat :=
  parensGe .sect $ seqGroup .allOrNone [text kw, (resolveWithPrec e .sect)]

def leftAssoc (left: Precedence) (right: Precedence) (op: Format) (behavior: FlattenBehavior) (f: PFormat) (es: List PFormat): PFormat :=
  if !es.isEmpty then
    let f := resolveWithPrec f left
    let es := es.map fun x => op ++ resolveWithPrec x right
    parensGe right $ seqGroup behavior $ f :: es
  else
    f

def app (f: PFormat) (es: List PFormat): PFormat :=
  leftAssoc .appL .appR "" .allOrNone f es

def parameterized (v: PFormat) (es: List PFormat): PFormat :=
  leftAssoc .parameterizedL .parameterizedR "" .fill v es

def define (v: PFormat) (es: List PFormat): PFormat :=
  leftAssoc .defineL .defineR "= " .fill v es

def andWhere (e: PFormat): PFormat :=
  leftAssoc .whereL .whereR "where" .fill e [token ""]

def rightAssoc (left: Precedence) (right: Precedence) (op: Format) (behavior: FlattenBehavior) (es: List PFormat) (r: PFormat): PFormat :=
  if !es.isEmpty then
    let es := es.map fun x => (resolveWithPrec x left) ++ op
    let r := resolveWithPrec r right
    parensGe left $ seqGroup behavior $ es ++ [r]
  else
    r

def arrow (es: List PFormat) (r: PFormat): PFormat :=
  rightAssoc .arrowL .arrowR " →" .fill es r

def lambdaArrow (es: List PFormat) (r: PFormat): PFormat :=
  let lambda (e: PFormat): PFormat :=
    rightAssoc .lambdaL .lambdaR "λ" .fill [token ""] e

  arrow (es.map (lambda ·)) r

def typing (v: PFormat) (t: PFormat): PFormat :=
  rightAssoc .typingL .typingR " :" .fill [v] t

def inExpr (es: List PFormat) (r: PFormat): PFormat :=
  rightAssoc .inL .inR " in" .fill es r

def infixAssoc (opPrec: Precedence) (opPrecS: Precedence) (op: Format) (es: List PFormat): PFormat :=
  match es with
  | [] => pnil
  | f :: [] => f
  | f :: e :: es =>
    let f := resolveWithPrec f opPrec
    let es := (e :: es).map fun x => op ++ (resolveWithPrec x opPrec)
    parensGe opPrecS $ seqGroup .fill $ f :: es

def stmts (es: List PFormat): PFormat :=
  infixAssoc .stmt .stmtS "; " es

def lmax (es: List PFormat): PFormat :=
  infixAssoc .lmax .lmaxS "⊔ " es

def ladd: Nat → PFormat → PFormat
| .zero, e => e
| .succ n, e => app (token "lsuc") [ladd n e]

def lconst: Nat → PFormat
| .zero => token "lzero"
| .succ n => ladd n (token "lone")

def levelBinderSeps: String × String := ⟨"{", "}"⟩
def implicitBinderSeps: String × String := ⟨"{", "}"⟩

def binderSeps (always: Bool): Lean.BinderInfo → (String × String)
| .default => if always then ("(", ")") else ⟨"", ""⟩
| .implicit | .strictImplicit => implicitBinderSeps
| .instImplicit => ⟨"{{", "}}"⟩

def lotBinderSeps (always: Bool): Option Lean.BinderInfo → (String × String)
| .none => levelBinderSeps
| .some x => binderSeps always x

def alwaysBinderSeps := binderSeps true
def maybeBinderSeps := binderSeps false
def alwaysLotBinderSeps := lotBinderSeps true
def maybeLotBinderSeps := lotBinderSeps false
