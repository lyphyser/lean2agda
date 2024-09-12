import Lean.Parser.Term

macro "genSubReader" "(" superType:term ")" "(" subType:term ")" fieldName:ident : command => `(
  instance {M: Type → Type} [Monad M] [base: MonadReaderOf $superType M]: MonadReaderOf $subType M where
    read := do pure (← base.read).$fieldName
)

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

def monadReaderOfOfMonadStateOf [MonadStateOf α M]: MonadReaderOf α M where
  read := get

def unitStateOf [Monad M]: MonadStateOf PUnit M where
  get := pure ()
  set _ := pure ()
  modifyGet f := pure (f ()).1
