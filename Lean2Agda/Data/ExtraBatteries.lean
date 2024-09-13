import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Batteries.Data.Vector.Basic

open Batteries (Vector)
open Std (HashMap)

namespace Fin

variable {M: Type u → Type v} [Monad M]

/-- Folds over `Fin n` from the left: `foldl 3 f x = f (f (f x 0) 1) 2`. -/
@[inline] def foldlM (n) (f : α → Fin n → M α) (init : α) : M α := loop init 0 where
  /-- Inner loop for `Fin.foldl`. `Fin.foldl.loop n f x i = f (f (f x i) ...) (n-1)`  -/
  loop (x : α) (i : Nat) : M α := do
    if h : i < n then loop (← f x ⟨i, h⟩) (i+1) else pure x
  termination_by n - i
  decreasing_by decreasing_trivial_pre_omega

/-- Folds over `Fin n` from the right: `foldr 3 f x = f 0 (f 1 (f 2 x))`. -/
@[inline] def foldrM (n) (f : Fin n → α → M α) (init : α) : M α := loop ⟨n, Nat.le_refl n⟩ init where
  /-- Inner loop for `Fin.foldr`. `Fin.foldr.loop n f i x = f 0 (f ... (f (i-1) x))`  -/
  loop : {i // i ≤ n} → α → M α
  | ⟨0, _⟩, x => pure x
  | ⟨i+1, h⟩, x => do loop ⟨i, Nat.le_of_lt h⟩ (← f ⟨i, h⟩ x)

end Fin

namespace Std.HashSet
@[inline]
protected def ofArray [BEq α] [Hashable α] (as : Array α) : HashSet α :=
  HashSet.empty.insertMany as
end Std.HashSet

def reverseHashMap {α} (a: Array α) {β} [BEq β] [Hashable β] (f: α → β) {γ} (g: Fin a.size → γ): HashMap β γ:=
  Fin.foldl a.size (init := Std.HashMap.empty) λ m i ↦
    m.insert (f a[i]) (g i)

def reverseVector {α} (a: Array α) {n: Nat} (f: α → Fin n) {γ} (init: γ) (g: Fin a.size → γ): Vector γ n :=
  Fin.foldl a.size (init := Vector.mkVector n init) λ m i ↦
    m.set (f a[i]) (g i)

variable {M : Type → Type} [Monad M] {ε} [Coe String ε] [MonadExcept ε M]

def toVector (a: Array α) (n: Nat) (desc: String): M (Vector α n) := do
  if h: a.size = n then
    pure ⟨a, h⟩
  else
    throw ↑s!"incorrect number of {desc}: {a.size} instead of {n}"

namespace Batteries.Vector
def mapM {α β} (f : α → M β) (v : Vector α n) : M (Vector β n) := do
  toVector (← v.toArray.mapM f) n "elements produced by mapM on Vector"
end Batteries.Vector

namespace Array
@[inline]
def backPop? (a: Array α): Option (α × Array α) :=
  let back := a.back?
  match back with
  | .some x => some (x, a.pop)
  | .none => none
end Array

instance {α : Type u} [Ord α] : Ord (Array α) where
  compare x y :=
    let rec loop (i : Nat) : Ordering :=
      if h₁ : i < x.size then
        if h₂ : i < y.size then
          let xi := x[i]'h₁
          let yi := y[i]'h₂
          match compare xi yi with
          | Ordering.eq   => loop (i + 1)
          | result        => result
        else
          Ordering.gt
      else if i < y.size then
        Ordering.lt
      else
        Ordering.eq
    loop 0

instance [Ord α] [Ord β] : Ord (α × β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

def commonPrefixLength {α : Type} [BEq α] (arr1 arr2 : Array α) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if h1: i < arr1.size then
      if h2: i < arr2.size then
        if arr1[i]'h1 == arr2[i]'h2 then
          loop (i + 1)
        else
          i
      else
        i
    else
      i
  loop 0

def compareName : Lean.Name → Lean.Name → Ordering
  | .anonymous, .anonymous => Ordering.eq
  | .anonymous, _ => Ordering.lt
  | _, .anonymous => Ordering.gt
  | .num n1 i1, .num n2 i2 =>
    match compareName n1 n2 with
    | Ordering.eq => compare i1 i2
    | r => r
  | .num _ _, _     => Ordering.lt
  | _, .num _ _     => Ordering.gt
  | .str n1 s1, .str n2 s2 =>
    match compareName n1 n2 with
    | Ordering.eq => compare s1 s2
    | r => r

instance : Ord Lean.Name where
  compare n1 n2 := compareName n1 n2

instance : LT Lean.Name where
  lt n1 n2 := compareName n1 n2 == Ordering.lt
