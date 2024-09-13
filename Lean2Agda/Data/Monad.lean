import Lean2Agda.Data.Value
import Lean.Parser.Term
import Lake.Util.EStateT

open Lake (EStateT EResult)

-- from Lake.Util.Lift, but we don't want to import it since it defines bad non-linear lifts using get instead of modifyGet

instance (priority := high) [MonadLift α β] : MonadLiftT α β := ⟨MonadLift.monadLift⟩

instance [Pure m] : MonadLiftT Id m where
  monadLift act := pure act.run

instance [Alternative m] : MonadLiftT Option m where
  monadLift
    | some a => pure a
    | none => failure

instance [Pure m] [MonadExceptOf ε m] : MonadLiftT (Except ε) m where
  monadLift
    | .ok a => pure a
    | .error e => throw e

instance [Bind m] [MonadReaderOf ρ m] [MonadLiftT n m] : MonadLiftT (ReaderT ρ n) m where
  monadLift act := do act (← read)

instance [Monad m] [Alternative m] [MonadLiftT n m] : MonadLiftT (OptionT n) m where
  monadLift act := act.run >>= liftM

instance [Monad m] [MonadExceptOf ε m] [MonadLiftT n m] : MonadLiftT (ExceptT ε n) m where
  monadLift act := act.run >>= liftM

instance [Monad m] [MonadExceptOf ε m] [MonadLiftT BaseIO m] : MonadLiftT (EIO ε) m where
  monadLift act := act.toBaseIO >>= liftM

-- high priority because we want this to be preferred over those that use get, and thus result in rc!=1, in case those happen to be imported accidentally
instance (priority := high - 1) [Inhabited σ] [Monad m] [MonadStateOf σ m] [MonadLiftT n m] : MonadLiftT (StateT σ n) m where
  monadLift act := do let (a, s) ← act (← modifyGet (·, default)); set s; pure a

instance (priority := high - 1) [Inhabited σ] [Monad m] [MonadStateOf σ m] [MonadExceptOf ε m] [MonadLiftT n m] : MonadLiftT (EStateT ε σ n) m where
  monadLift act :=
    (modifyGet (·, default)
      >>= λ s ↦ liftM <| EStateT.run s act)
      >>= λ r ↦
        match r with
        | .ok x s => set s *> pure x
        | .error e s => set s *> throw e

instance (priority := high - 1) [Inhabited σ] [Monad m] [MonadStateOf σ m] [MonadExceptOf ε m] : MonadLift (EStateM ε σ) m where
  monadLift act :=
    ((EStateM.run act ·) <$> modifyGet (·, default))
      >>= λ r ↦
        match r with
        | EStateM.Result.ok x s => set s *> pure x
        | .error e s => set s *>  throw e


macro "genSubMonad" "(" superType:term ")" "(" subType:term ")" fieldLValue:Lean.Parser.Term.structInstLVal fieldName:ident : command => `(
  instance {M: Type → Type} [Monad M] [base: MonadStateOf $superType M]: MonadStateOf $subType M where
    get := do pure (← base.get).$fieldName
    modifyGet f := do pure (← base.modifyGet (λ σ ↦
      let v := σ.$fieldName
      let σ := {σ with $fieldLValue := default}
      let (r, σ') := f v
      (r, {σ with $fieldLValue := σ'})
    ))
    set σ' := base.modifyGet (λ σ ↦ ((), {σ with $fieldLValue := σ'}))
)

def unitStateOf [Monad M]: MonadStateOf PUnit M where
  get := pure ()
  set _ := pure ()
  modifyGet f := pure (f ()).1

namespace Lake.EResult
def act [Monad m] [MonadStateOf σ m] [MonadExceptOf ε m] (r: EResult ε σ α): m α := do
  match r with
  | .ok a s =>
    set s
    pure a
  | .error e s =>
    set s
    throw e
end Lake.EResult

instance EStateT.monadControl (σ : Type u) (m : Type u → Type v) [Monad m] : MonadControl m (EStateT ε σ m) where
  stM α := EResult ε σ α
  liftWith f := do let s ← get; liftM (f (·.run s))
  restoreM x := do let r ← liftM x; λ _ ↦ pure r

def SubState (σ) (α) := σ → ((α × (σ → σ)) × σ)

namespace SubState
def mk (enter: σ → (α × β) × σ) (exit: β → σ → σ): SubState σ α :=
  λ s ↦
    let ((a, b), s) := enter s
    ((a, λ s ↦ exit b s), s)

def mkPure (a: α): SubState σ α :=
  λ s ↦ ((a, id), s)

def compose (a: SubState σ α) (b: α → SubState σ β): SubState σ β :=
  λ s ↦
    let ((va, pa), s) := a s
    let ((vb, pb), s) := b va s
    ((vb, λ s ↦ pa (pb s)), s)

def withMe (s: SubState σ α) {m} [Monad m] [MonadStateOf σ m] (act: α → m β): m β := do
  let (v, post) ← modifyGet s
  let r ← act v
  modify post
  pure r

def permanentFn (a: SubState σ α): σ → (α × σ) :=
  λ s ↦
    let ((r, _), s) := (a s)
    (r, s)

def permanently (s: SubState σ α) {m} [Monad m] [MonadStateOf σ m]: m α := do
  modifyGet s.permanentFn

def lift [MonadStateOf σ (StateM σ')] (a: SubState σ α): SubState σ' α :=
  let a: StateM σ' _ := modifyGet a
  let f := λ (a, p) ↦
    let p: StateM σ' _ := modify p
    (a, λ s ↦ (Id.run <| StateT.run p s).2)
  Id.run <| StateT.run (f <$> a)

instance [MonadStateOf σ (StateM σ')]: Coe (SubState σ α) (SubState σ' α) := ⟨lift⟩

end SubState
