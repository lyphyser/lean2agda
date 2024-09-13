import Lean2Agda.Data.Monad
import Lean.Meta.Basic

open Lean (MessageData)
open Lean.Meta (MetaM)

local macro "M": term => `(ExceptT MessageData MetaM)

open Lean

private structure ExprTyStructEq where
  val : ExprStructEq
  ty : Option ExprStructEq
  deriving Inhabited, BEq, Hashable

open Lean.Meta in
/-- Correct implicitness of lambdas -/
partial def fixExpr
    (input : Expr)
    (expectedType : Option Expr )
    (usedLetOnly := false)
    : M Expr := do
  let _ : STWorld IO.RealWorld M := ⟨⟩
  let _ : MonadLiftT (ST IO.RealWorld) M := { monadLift := fun x => liftM (m := MetaM) (liftM (m := ST IO.RealWorld) x) }

  let rec visit (e : Expr) (ty : Option Expr) : MonadCacheT ExprTyStructEq Expr M Expr :=
    checkCache { val := e, ty : ExprTyStructEq } fun _ => Meta.withIncRecDepth do
      let rec visitLambda (fvars : Array Expr) (e : Expr) (ty: Option Expr): MonadCacheT ExprTyStructEq Expr M Expr := do
        match e with
        | Expr.lam n d b c =>
          let (bt, c) ← match ty with
          | .none => pure (none, c)
          | .some ty =>
            let ty ← whnf ty
            match ty with
            | .forallE n' d' b' c' =>
              withLocalDecl n' c' d' fun x =>
                pure (some (b'.instantiate1 x), c')
            | _ =>
              throwThe _ m!"pi type expected\nexpression: {indentExpr e}\nexpected type: {indentExpr ty}"
              pure (none, c)
          withLocalDecl n c (← visit (d.instantiateRev fvars) none) fun x =>
            visitLambda (fvars.push x) b bt
        | e => mkLambdaFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars) ty)
      let rec visitForall (fvars : Array Expr) (e : Expr) : MonadCacheT ExprTyStructEq Expr M Expr := do
        match e with
        | Expr.forallE n d b c =>
          withLocalDecl n c (← visit (d.instantiateRev fvars) none) fun x =>
            visitForall (fvars.push x) b
        | e => mkForallFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars) none)
      let rec visitLet (fvars : Array Expr) (e : Expr) : MonadCacheT ExprTyStructEq Expr M Expr := do
        match e with
        | Expr.letE n t v b _ =>
          let ty ← visit (t.instantiateRev fvars) none
          withLetDecl n ty (← visit (v.instantiateRev fvars) (some ty)) fun x =>
            visitLet (fvars.push x) b
        | e => mkLetFVars (usedLetOnly := usedLetOnly) fvars (← visit (e.instantiateRev fvars) none)
      match e with
      | .forallE .. => visitForall #[] e
      | .lam .. => visitLambda #[] e ty
      | .letE .. => visitLet #[] e
      | .app f b =>
        let f := ← visit f none
        let mut ft := none
        match ← whnf (← inferType f) with
          | .forallE _ d _ _ =>
            ft := some d
          | _ => throwThe _ m!"function expected: {indentExpr e}"
        let b := ← visit b ft
        pure <| e.updateApp! f b
      | .mdata _ b => pure <| e.updateMData! (← visit b ty)
      | .proj _ _ b => pure <| e.updateProj! (← visit b none)
      | e => pure e
  /-
  let visit' (e : Expr) (ty : Option Expr) : MonadCacheT ExprTy Expr m Expr := do
    let ty ← match ty with
    | .some ty => pure <| some (← visit ty none)
    | .none => pure none
    visit e ty
  -/
  visit input expectedType |>.run
