/--
Typeclass used to implicitly provide function arguments in an inheritable way.

It can replace [`MonadReaderOf `] or the ReaderT monad transformer.

To provide a value you can use:
- have := mkValue <value>
- have := mkValueAs α <value>

To use a value you can use:
- [Value α] ... value
- [Value α] ... valueOf α
- [a: Value α] ... ↑a
- [a: Value α] ... a.val
- [a: Value α] ... a

It has the same signature as `Inhabited`, but is for explicitly specified values.
-/
class Value (α) where
  val: α

def mkValue {α} (x: α): Value α := ⟨x⟩

def mkValueAs (α) (x: α): Value α := ⟨x⟩

def getValue {m} [Monad m] {α} [MonadState α m]: m (Value α) := mkValue <$> get
def getTheValue {m} [Monad m] (α) [MonadStateOf α m]: m (Value α) := mkValue <$> getThe α

def value {α} [Value α]: α :=
  Value.val

def valueOf (α) [Value α]: α :=
  Value.val

instance: Coe (Value α) α where
  coe x := x.val

macro "genSubValue" "(" superType:term ")" "(" subType:term ")" fieldName:ident : command => `(
  instance [base: Value $superType]: Value $subType where
    val := base.val.$fieldName
)
