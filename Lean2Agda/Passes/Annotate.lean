import Lean2Agda.Data.Monad
import Lean2Agda.Data.Value
import Lean.Meta.Basic
import Batteries.Data.Vector.Basic

open Batteries (Vector)
open Lean
open Lake (EStateT)

def binderToFin: BinderInfo → Fin 4
| .default => 0
| .implicit => 1
| .strictImplicit => 2
| .instImplicit => 3

def intToBinder: Int → BinderInfo
| 0 => .default
| 1 => .implicit
| 2 => .strictImplicit
| 3 => .instImplicit
| _ => .implicit

def optionIntToBinder: Option Int → BinderInfo
| .none => .default
| .some x => intToBinder x

structure AnnotateContext where
  binderMDatas: Vector KVMap 4
  implicitKeyword: Name
  projectKeyword: Name

structure AnnotationData where
  projectionLevels: Array (List Level) := #[]
  deriving Inhabited

local macro "M": term => `(EStateT MessageData AnnotationData MetaM)
variable [Value AnnotateContext]

open Lean.Meta in
def annotateApp
    (e : Expr): M Expr := do
  match e with
  | Expr.app f b => do
    let ft ← inferType f
    let ft ← whnf ft
    if let .forallE _ _ _ bi := ft then
      let f ← annotateApp f
      let e := e.updateApp! f b
      --IO.println s!"-- app: {implicit}: {e} === {ft}"
      if bi != .default then
        let m := (valueOf AnnotateContext).binderMDatas[binderToFin bi]
        pure $ .mdata m e
      else
        pure $ e
    else
      throw ↑s!"unexpected function type {ft}"
  | _ => return e

private def unwrap: Expr → Expr
| .app f _ => unwrap f
| .lam _ _ b _ => unwrap b
| .mdata _ e => e
| e => e

open Lean.Meta in
def annotateProj
    (e : Expr): M Expr := do
  match e with
  | Expr.proj typeName _projIdx structExpr => do
    let structType ← inferType structExpr
    let structType ← whnf structType -- TODO: needed?
    let structType := unwrap structType
    if let .const structTypeName typeLevels := structType then
      if structTypeName != typeName then
        throw ↑s!"structTypeName differs from typeName: {structTypeName} {typeName}"

      let idx <- modifyGet fun st => (st.projectionLevels.size, {st with projectionLevels := st.projectionLevels.push (typeLevels)})
      let m := KVMap.empty.setNat (valueOf AnnotateContext).projectKeyword idx
      pure <| .mdata m e
    else
      throw ↑s!"structType is not a const: {structType}"
      pure  e
  | _ => return e

def annotateExpr
  (e : Expr) : M Expr :=
  Meta.transform (m := M) e (post := fun e => do
    match e with
    | Expr.app _ _ => return .done (← annotateApp e)
    | Expr.proj _ _ _ => return .done (← annotateProj e)
    | _ => return .continue
  )

def annotateProjs
  (e : Expr) : M Expr :=
  Meta.transform (m := M) e (post := fun e => do
    match e with
    | Expr.proj _ _ _ => return .done (← annotateProj e)
    | _ => return .continue
  )
