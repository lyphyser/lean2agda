{-# OPTIONS --prop --type-in-type #-}
open Agda.Primitive

Type : (u : Level) → Set (lsuc (lsuc u))
Type u = Set (lsuc u)

lone : Level
lone = lsuc lzero

--inductive 1 2->1 1 2
data Eq#n {u-1 : Level} {α : Set u-1} : α → α → Prop where
  Eq:refl#n : (a : α) → Eq#n {u-1} {α} a a

--inductive 0 0->0 0 0
data Nat : Set₁ where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

--def
#0 : Nat → Nat → Prop
#0 = Eq#n {lone} {Nat}

--record 1 2->2 0 3
record OfNat {u : Level} (α : Type u) (x$ : Nat) : Type u where
  constructor OfNat:mk
  field
    ofNat : α

--def
#1 : Nat → Set₁
#1 = OfNat {lzero} Nat

--def
OfNat:ofNat : {u : Level} → {α : Type u} → (x$ : Nat) → {{OfNat {u} α x$}} → α
OfNat:ofNat {u} {α} x$ {{self}} = OfNat.ofNat {u} self

--def
#2 : (x$ : Nat) → {{#1 x$}} → Nat
#2 = OfNat:ofNat {lzero} {Nat}

--def
instOfNatNat : (n : Nat) → #1 n
instOfNatNat n = OfNat:mk {lzero} {Nat} {n} n

--def
#3 : #1 0
#3 = instOfNatNat 0

--def
#4 : Nat
#4 = #2 0 {{#3}}

--recursor 2->1 1->2 1 1
Eq:rec#zn :
  {u-1 : Level} →
    {α : Set u-1} →
      {a$ : α} →
        {motive : (a$1 : α) → Eq#n {u-1} {α} a$ a$1 → Prop} →
          motive a$ (Eq:refl#n {u-1} {α} a$) → {a$1 : α} → (t : Eq#n {u-1} {α} a$ a$1) → motive a$1 t
Eq:rec#zn {u-1} {α} {a$} {motive} refl {_} (Eq:refl#n a$) = refl

--def
Eq:ndrec#zn : {u2 : Level} → {α : Set u2} → {a : α} → {motive : α → Prop} → motive a → {b : α} → Eq#n {u2} {α} a b → motive b
Eq:ndrec#zn {u2} {α} {a} {motive} m {b} h = Eq:rec#zn {u2} {α} {a} {λ (x$ : α) → λ (_ : Eq#n {u2} {α} a x$) → motive x$} m {b} h

--def
#5 : {a : Nat} → {motive : Nat → Prop} → motive a → {b : Nat} → #0 a b → motive b
#5 {a} {motive} = Eq:ndrec#zn {lone} {Nat} {a} {motive}

--def
#7 : Set₁
#7 = Nat

--def
#20 : #7 → Set₁
#20 _ = #7

--record 2 2->2 0 4
record PSigma#nn {u : Level} {v : Level} {α : Set u} (β : α → Set v) : Set (lone ⊔ u ⊔ v) where
  constructor PSigma:mk#nn
  field
    fst : α
    snd : β fst

--def
#21 : Set₁
#21 = PSigma#nn {lone} {lone} {#7} #20

--def
#22 : #7 → #7 → #21
#22 = PSigma:mk#nn {lone} {lone} {#7} {#20}

--recursor 2->2 0->0 1 1
PSigma:rec#nnn :
  {u-1 : Level} → {u : Level} → {v : Level} →
    {α : Set u} →
      {β : α → Set v} →
        {motive : PSigma#nn {u} {v} {α} β → Set u-1} →
          ((fst : α) → (snd : β fst) → motive (PSigma:mk#nn {u} {v} {α} {β} fst snd)) → (t : PSigma#nn {u} {v} {α} β) → motive t
PSigma:rec#nnn {u-1} {u} {v} {α} {β} {motive} mk (PSigma:mk#nn fst snd) = mk fst snd

--def
PSigma:casesOn#nnn :
  {u-1 : Level} → {u : Level} → {v : Level} →
    {α : Set u} →
      {β : α → Set v} →
        {motive : PSigma#nn {u} {v} {α} β → Set u-1} →
          (t : PSigma#nn {u} {v} {α} β) → ((fst : α) → (snd : β fst) → motive (PSigma:mk#nn {u} {v} {α} {β} fst snd)) → motive t
PSigma:casesOn#nnn {u-1} {u} {v} {α} {β} {motive} t mk
  = PSigma:rec#nnn {u-1} {u} {v} {α} {β} {motive} (λ (fst : α) → λ (snd : β fst) → mk fst snd) t

--def
#23 : {motive : #21 → Set₁} → (t : #21) → ((fst : #7) → (snd : #7) → motive (#22 fst snd)) → motive t
#23 {motive} = PSigma:casesOn#nnn {lone} {lone} {lone} {#7} {#20} {motive}

--inductive 1 2->2 1 3
data Acc#n {u : Level} {α : Set u} (r : α → α → Prop) : α → Prop where
  Acc:intro#n : (x : α) → ((y : α) → r y x → Acc#n {u} {α} r y) → Acc#n {u} {α} r x

--record 1 2->2 0 3
record WellFounded#n {u : Level} {α : Set u} (r : α → α → Prop) : Prop where
  constructor WellFounded:intro#n
  field
    h : (a : α) → Acc#n {u} {α} r a

--record 1 1->1 0 2
record WellFoundedRelation#n {u : Level} (α : Set u) : Set (lone ⊔ u) where
  constructor WellFoundedRelation:mk#n
  field
    rel : α → α → Prop
    wf : WellFounded#n {u} {α} rel

--record 1 1->1 0 2
record SizeOf#n {u : Level} (α : Set u) : Set (lone ⊔ u) where
  constructor SizeOf:mk#n
  field
    sizeOf : α → Nat

--def
instSizeOfNat : SizeOf#n {lone} Nat
instSizeOfNat = SizeOf:mk#n {lone} {Nat} (λ (n : Nat) → n)

--def
InvImage#nn : {u : Level} → {v : Level} → {α : Set u} → {β : Set v} → (β → β → Prop) → (α → β) → α → α → Prop
InvImage#nn {u} {v} {α} {β} r f a₁ a₂ = r (f a₁) (f a₂)

--def
WellFoundedRelation:rel#n : {u : Level} → {α : Set u} → {{WellFoundedRelation#n {u} α}} → α → α → Prop
WellFoundedRelation:rel#n {u} {α} {{self}} = WellFoundedRelation#n.rel {u} self

--def
rfl#n : {u : Level} → {α : Set u} → {a : α} → Eq#n {u} {α} a a
rfl#n {u} {α} {a} = Eq:refl#n {u} {α} a

--recursor 2->2 1->1 1 1
postulate
  Acc:rec#zn :
    {u : Level} →
      {α : Set u} →
        {r : α → α → Prop} →
          {motive : (a$ : α) → Acc#n {u} {α} r a$ → Prop} →
            ((x : α) →
              (h : (y : α) → r y x → Acc#n {u} {α} r y) →
                ((y : α) → (a$ : r y x) → motive y (h y a$)) → motive x (Acc:intro#n {u} {α} {r} x h)) →
              {a$ : α} → (t : Acc#n {u} {α} r a$) → motive a$ t

--def
-private:Init:WF:0:InvImage:accAux#nn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {β : Set v} →
        {r : β → β → Prop} →
          (f : α → β) →
            {b : β} → Acc#n {v} {β} r b → (x : α) → Eq#n {v} {β} (f x) b → Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) x
-private:Init:WF:0:InvImage:accAux#nn {u} {v} {α} {β} {r} f {b} ac
  = Acc:rec#zn {v}
    {β}
    {r}
    {λ (b# : β) →
      λ (_ : Acc#n {v} {β} r b#) → (x : α) → Eq#n {v} {β} (f x) b# → Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) x}
    (λ (x : β) →
      λ (acx : (y : β) → r y x → Acc#n {v} {β} r y) →
        λ (ih : (y : β) → r y x → (x# : α) → Eq#n {v} {β} (f x#) y → Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) x#) →
          λ (z : α) →
            λ (e : Eq#n {v} {β} (f z) x) →
              Acc:intro#n {u}
                {α}
                {InvImage#nn {u} {v} {α} {β} r f}
                z
                (λ (y : α) →
                  λ (lt : InvImage#nn {u} {v} {α} {β} r f y z) →
                    Eq:ndrec#zn {v}
                      {β}
                      {f z}
                      {λ (x# : β) →
                        ((y# : β) → r y# x# → Acc#n {v} {β} r y#) →
                          ((y# : β) →
                            r y# x# → (x#1 : α) → Eq#n {v} {β} (f x#1) y# → Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) x#1) →
                            Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) y}
                      (λ (_ : (y# : β) → r y# (f z) → Acc#n {v} {β} r y#) →
                        λ
                          (ih# :
                            (y# : β) →
                              r y# (f z) →
                                (x# : α) → Eq#n {v} {β} (f x#) y# → Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) x#) →
                          ih# (f y) lt y (rfl#n {v} {β} {f y}))
                      {x}
                      e
                      acx
                      ih))
    {b}
    ac

--theorem
InvImage:accessible#nn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {β : Set v} →
        {r : β → β → Prop} → {a : α} → (f : α → β) → Acc#n {v} {β} r (f a) → Acc#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f) a
InvImage:accessible#nn {u} {v} {α} {β} {r} {a} f ac
  = -private:Init:WF:0:InvImage:accAux#nn {u} {v} {α} {β} {r} f {f a} ac a (rfl#n {v} {β} {f a})

--recursor 2->2 0->0 1 1
WellFounded:rec#zn :
  {u : Level} →
    {α : Set u} →
      {r : α → α → Prop} →
        {motive : WellFounded#n {u} {α} r → Prop} →
          ((h : (a : α) → Acc#n {u} {α} r a) → motive (WellFounded:intro#n {u} {α} {r} h)) → (t : WellFounded#n {u} {α} r) → motive t
WellFounded:rec#zn {u} {α} {r} {motive} intro (WellFounded:intro#n h) = intro h

--theorem
WellFounded:apply#n : {u : Level} → {α : Set u} → {r : α → α → Prop} → WellFounded#n {u} {α} r → (a : α) → Acc#n {u} {α} r a
WellFounded:apply#n {u} {α} {r} wf a
  = WellFounded:rec#zn {u}
    {α}
    {r}
    {λ (_ : WellFounded#n {u} {α} r) → (x$ : α) → Acc#n {u} {α} r x$}
    (λ (p : (a# : α) → Acc#n {u} {α} r a#) → p)
    wf
    a

--theorem
InvImage:wf#nn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {β : Set v} →
        {r : β → β → Prop} → (f : α → β) → WellFounded#n {v} {β} r → WellFounded#n {u} {α} (InvImage#nn {u} {v} {α} {β} r f)
InvImage:wf#nn {u} {v} {α} {β} {r} f h
  = WellFounded:intro#n {u}
    {α}
    {InvImage#nn {u} {v} {α} {β} r f}
    (λ (a : α) → InvImage:accessible#nn {u} {v} {α} {β} {r} {a} f (WellFounded:apply#n {v} {β} {r} h (f a)))

--theorem
WellFoundedRelation:wf#n :
  {u : Level} →
    {α : Set u} → {{self : WellFoundedRelation#n {u} α}} → WellFounded#n {u} {α} (WellFoundedRelation:rel#n {u} {α} {{self}})
WellFoundedRelation:wf#n {u} {α} {{self}} = WellFoundedRelation#n.wf {u} self

--theorem
invImage:proof-1#nn :
  {u-1 : Level} → {u-2 : Level} →
    {α : Set u-1} →
      {β : Set u-2} →
        (f : α → β) →
          (h : WellFoundedRelation#n {u-2} β) →
            WellFounded#n {u-1} {α} (InvImage#nn {u-1} {u-2} {α} {β} (WellFoundedRelation:rel#n {u-2} {β} {{h}}) f)
invImage:proof-1#nn {u-1} {u-2} {α} {β} f h
  = InvImage:wf#nn {u-1} {u-2}
    {α}
    {β}
    {WellFoundedRelation:rel#n {u-2} {β} {{h}}}
    f
    (WellFoundedRelation:wf#n {u-2} {β} {{h}})

--def
invImage#nn :
  {u-1 : Level} → {u-2 : Level} → {α : Set u-1} → {β : Set u-2} → (α → β) → WellFoundedRelation#n {u-2} β → WellFoundedRelation#n {u-1} α
invImage#nn {u-1} {u-2} {α} {β} f h
  = WellFoundedRelation:mk#n {u-1}
    {α}
    (InvImage#nn {u-1} {u-2} {α} {β} (WellFoundedRelation:rel#n {u-2} {β} {{h}}) f)
    (invImage:proof-1#nn {u-1} {u-2} {α} {β} f h)

--record 1 1->1 0 2
record LT {u : Level} (α : Type u) : Type u where
  constructor LT:mk
  field
    lt : α → α → Prop

--inductive 0 1->1 1 1
data Nat:le (n : Nat) : Nat → Prop where
  Nat:le:refl : Nat:le n n
  Nat:le:step : {m : Nat} → Nat:le n m → Nat:le n (Nat:succ m)

--def
Nat:lt : Nat → Nat → Prop
Nat:lt n m = Nat:le (Nat:succ n) m

--def
instLTNat : LT {lzero} Nat
instLTNat = LT:mk {lzero} {Nat} Nat:lt

--def
LT:lt : {u : Level} → {α : Type u} → {{LT {u} α}} → α → α → Prop
LT:lt {u} {α} {{self}} = LT.lt {u} self

--def
#26 : Nat → Nat → Prop
#26 = LT:lt {lzero} {Nat} {{instLTNat}}

--def
#27 : Nat → Nat → Prop
#27 x1$ x2$ = #26 x1$ x2$

--def
#28 : Nat → Prop
#28 = Acc#n {lone} {Nat} #27

--def
#29 : (x : Nat) → ((y : Nat) → #26 y x → #28 y) → #28 x
#29 = Acc:intro#n {lone} {Nat} {#27}

--inductive 0 2->2 0 2
data Or (a : Prop) (b : Prop) : Prop where
  Or:inl : a → Or a b
  Or:inr : b → Or a b

--inductive 0 0->0 0 0
data False : Prop where

--def
Not : Prop → Prop
Not a = a → False

--recursor 0->0 0->0 1 0
False:rec#z : (motive : False → Prop) → (t : False) → motive t
False:rec#z  _ ()

--def
absurd#z : {a : Prop} → {b : Prop} → a → Not a → b
absurd#z {a} {b} h₁ h₂ = False:rec#z (λ (_ : False) → b) (h₂ h₁)

--def
letFun#zz : {α : Prop} → {β : α → Prop} → (v : α) → ((x : α) → β x) → β v
letFun#zz {α} {β} v f = f v

--def
Acc:recOn#zn :
  {u : Level} →
    {α : Set u} →
      {r : α → α → Prop} →
        {motive : (a$ : α) → Acc#n {u} {α} r a$ → Prop} →
          {a$ : α} →
            (t : Acc#n {u} {α} r a$) →
              ((x : α) →
                (h : (y : α) → r y x → Acc#n {u} {α} r y) →
                  ((y : α) → (a$1 : r y x) → motive y (h y a$1)) → motive x (Acc:intro#n {u} {α} {r} x h)) →
                motive a$ t
Acc:recOn#zn {u} {α} {r} {motive} {a$} t intro = Acc:rec#zn {u} {α} {r} {motive} intro {a$} t

--theorem
Acc:inv#n : {u : Level} → {α : Set u} → {r : α → α → Prop} → {x : α} → {y : α} → Acc#n {u} {α} r x → r y x → Acc#n {u} {α} r y
Acc:inv#n {u} {α} {r} {x} {y} h₁ h₂
  = Acc:recOn#zn {u}
    {α}
    {r}
    {λ (x$ : α) → λ (_ : Acc#n {u} {α} r x$) → r y x$ → Acc#n {u} {α} r y}
    {x}
    h₁
    (λ (x$ : α) →
      λ (ac₁ : (y# : α) → r y# x$ → Acc#n {u} {α} r y#) →
        λ (_ : (y# : α) → r y# x$ → r y y# → Acc#n {u} {α} r y) → λ (h₂# : r y x$) → ac₁ y h₂#)
    h₂

--record 1 1->1 0 2
record Add {u : Level} (α : Type u) : Type u where
  constructor Add:mk
  field
    add : α → α → α

--def
#41 : #7 → Set₁
#41 _ = #7 → Nat

--def
#43#n : {u : Level} → Type u
#43#n {u} = Nat → Set u

--record 2 2->2 0 4
record PProd#nn {u : Level} {v : Level} (α : Set u) (β : Set v) : Set (lone ⊔ u ⊔ v) where
  constructor PProd:mk#nn
  field
    fst : α
    snd : β

--record 1 0->0 0 1
record PUnit#n {u : Level} : Set u where
  constructor PUnit:unit#n

--recursor 0->0 0->0 1 2
Nat:rec#n : {u : Level} → {motive : #43#n {u}} → motive Nat:zero → ((n : Nat) → motive n → motive (Nat:succ n)) → (t : Nat) → motive t
Nat:rec#n {u} {motive} zero _ (Nat:zero) = zero
Nat:rec#n {u} {motive} zero succ (Nat:succ n) = succ n (Nat:rec#n {u} {motive} zero succ n)

--def
Nat:below#n : {u : Level} → {#43#n {u}} → Nat → Set (lone ⊔ u)
Nat:below#n {u} {motive} t
  = Nat:rec#n {lsuc (lone ⊔ u)}
    {λ (_ : Nat) → Set (lone ⊔ u)}
    (PUnit#n {lone ⊔ u})
    (λ (n : Nat) → λ (n-ih : Set (lone ⊔ u)) → PProd#nn {u} {lone ⊔ u} (motive n) n-ih)
    t

--def
#42 : Nat → Set₁
#42 = Nat:below#n {lone} {#41}

--def
Nat:brecOn#n : {u : Level} → {motive : #43#n {u}} → (t : Nat) → ((t# : Nat) → Nat:below#n {u} {motive} t# → motive t#) → motive t
Nat:brecOn#n {u} {motive} t F-1
  = PProd#nn.fst {u} {lone ⊔ u}
    (Nat:rec#n {lone ⊔ u}
      {λ (t# : Nat) → PProd#nn {u} {lone ⊔ u} (motive t#) (Nat:below#n {u} {motive} t#)}
      (PProd:mk#nn {u} {lone ⊔ u}
        {motive Nat:zero}
        {PUnit#n {lone ⊔ u}}
        (F-1 Nat:zero (PUnit:unit#n {lone ⊔ u}))
        (PUnit:unit#n {lone ⊔ u}))
      (λ (n : Nat) →
        λ (n-ih : PProd#nn {u} {lone ⊔ u} (motive n) (Nat:below#n {u} {motive} n)) →
          PProd:mk#nn {u} {lone ⊔ u}
            {motive (Nat:succ n)}
            {PProd#nn {u} {lone ⊔ u} (motive n) (Nat:below#n {u} {motive} n)}
            (F-1 (Nat:succ n) n-ih)
            n-ih)
      t)

--def
#44#n : {u-1 : Level} → Type u-1
#44#n {u-1} = #7 → #7 → Set u-1

--def
Nat:casesOn#n : {u : Level} → {motive : #43#n {u}} → (t : Nat) → motive Nat:zero → ((n : Nat) → motive (Nat:succ n)) → motive t
Nat:casesOn#n {u} {motive} t zero succ = Nat:rec#n {u} {motive} zero (λ (n : Nat) → λ (_ : motive n) → succ n) t

--def
Nat:add:match-1#n :
  {u-1 : Level} →
    (motive : #44#n {u-1}) →
      (x$ : #7) → (x$1 : #7) → ((a : #7) → motive a Nat:zero) → ((a : #7) → (b : Nat) → motive a (Nat:succ b)) → motive x$ x$1
Nat:add:match-1#n {u-1} motive x$ x$1 h-1 h-2 = Nat:casesOn#n {u-1} {λ (x : #7) → motive x$ x} x$1 (h-1 x$) (λ (n$ : Nat) → h-2 x$ n$)

--def
Nat:add : #7 → #7 → Nat
Nat:add x$ x$1
  = Nat:brecOn#n {lone}
    {#41}
    x$1
    (λ (x$2 : #7) →
      λ (f : #42 x$2) →
        λ (x$3 : #7) →
          Nat:add:match-1#n {lone}
            (λ (_ : #7) → λ (x$4 : #7) → #42 x$4 → Nat)
            x$3
            x$2
            (λ (a : #7) → λ (_ : #42 Nat:zero) → a)
            (λ (a : #7) → λ (b : Nat) → λ (x$4 : #42 (Nat:succ b)) → Nat:succ (PProd#nn.fst {lone} {lone} x$4 a))
            f)
    x$

--def
instAddNat : Add {lzero} Nat
instAddNat = Add:mk {lzero} {Nat} Nat:add

--def
outParam#n : {u : Level} → Set u → Set u
outParam#n {u} α = α

--def
#45 : {w : Level} → Type (lsuc w)
#45 {w} = outParam#n {lsuc (lsuc w)} (Type w)

--record 3 3->3 0 6
record HAdd {u : Level} {v : Level} {w : Level} (α : Type u) (β : Type v) (γ : #45 {w}) : Type (u ⊔ v ⊔ w) where
  constructor HAdd:mk
  field
    hAdd : α → β → γ

--def
Add:add : {u : Level} → {α : Type u} → {{Add {u} α}} → α → α → α
Add:add {u} {α} {{self}} = Add.add {u} self

--def
instHAdd : {u-1 : Level} → {α : Type u-1} → {{Add {u-1} α}} → HAdd {u-1} {u-1} {u-1} α α α
instHAdd {u-1} {α} {{inst$}} = HAdd:mk {u-1} {u-1} {u-1} {α} {α} {α} (λ (a : α) → λ (b : α) → Add:add {u-1} {α} {{inst$}} a b)

--def
HAdd:hAdd :
  {u : Level} → {v : Level} → {w : Level} → {α : Type u} → {β : Type v} → {γ : #45 {w}} → {{HAdd {u} {v} {w} α β γ}} → α → β → γ
HAdd:hAdd {u} {v} {w} {α} {β} {γ} {{self}} = HAdd.hAdd {u} {v} {w} self

--def
#16 : Nat → Nat → Nat
#16 = HAdd:hAdd {lzero} {lzero} {lzero} {Nat} {Nat} {Nat} {{instHAdd {lzero} {Nat} {{instAddNat}}}}

--def
#17 : Nat
#17 = #2 1 {{instOfNatNat 1}}

--def
#30 : Set₁
#30 = Nat → Prop

--record 1 1->1 0 2
record LE {u : Level} (α : Type u) : Type u where
  constructor LE:mk
  field
    le : α → α → Prop

--def
instLENat : LE {lzero} Nat
instLENat = LE:mk {lzero} {Nat} Nat:le

--def
LE:le : {u : Level} → {α : Type u} → {{LE {u} α}} → α → α → Prop
LE:le {u} {α} {{self}} = LE.le {u} self

--def
#31 : Nat → #30
#31 = LE:le {lzero} {Nat} {{instLENat}}

--def
#32 : Nat → Prop
#32 x$ = (x$1 : Nat) → #31 x$ x$1 → Or (#0 x$ x$1) (#26 x$ x$1)

--def
#43#z : Set₁
#43#z = Nat → Prop

--record 2 2->2 0 3
record PProd#zn {v : Level} (α : Prop) (β : Set v) : Set (lone ⊔ v) where
  constructor PProd:mk#zn
  field
    fst : α
    snd : β

--def
Nat:below#z : {#43#z} → Nat → Set₁
Nat:below#z {motive} t
  = Nat:rec#n {lsuc lone}
    {λ (_ : Nat) → Set₁}
    (PUnit#n {lone})
    (λ (n : Nat) → λ (n-ih : Set₁) → PProd#zn {lone} (motive n) n-ih)
    t

--def
#33 : Nat → Set₁
#33 = Nat:below#z {#32}

--def
#34 : #30
#34 = #31 Nat:zero

--def
#35 : Set₁
#35 = #33 Nat:zero

--def
#36 : Set₁
#36 = Nat → Prop

--def
#37 : #36
#37 = #0 Nat:zero

--def
#38 : Set₁
#38 = Nat → Prop

--def
#39 : #38
#39 = #26 Nat:zero

--def
#40 : {a : Nat} → #0 a a
#40 {a} = rfl#n {lone} {Nat} {a}

--def
Nat:brecOn#z : {motive : #43#z} → (t : Nat) → ((t# : Nat) → Nat:below#z {motive} t# → motive t#) → motive t
Nat:brecOn#z {motive} t F-1
  = PProd#zn.fst {lone}
    (Nat:rec#n {lone}
      {λ (t# : Nat) → PProd#zn {lone} (motive t#) (Nat:below#z {motive} t#)}
      (PProd:mk#zn {lone} {motive Nat:zero} {PUnit#n {lone}} (F-1 Nat:zero (PUnit:unit#n {lone})) (PUnit:unit#n {lone}))
      (λ (n : Nat) →
        λ (n-ih : PProd#zn {lone} (motive n) (Nat:below#z {motive} n)) →
          PProd:mk#zn {lone}
            {motive (Nat:succ n)}
            {PProd#zn {lone} (motive n) (Nat:below#z {motive} n)}
            (F-1 (Nat:succ n) n-ih)
            n-ih)
      t)

--theorem
Nat:le-succ : (n : Nat) → #31 n (Nat:succ n)
Nat:le-succ n = Nat:le:step {n} {n} (Nat:le:refl {n})

--theorem
Eq:symm#n : {u : Level} → {α : Set u} → {a : α} → {b : α} → Eq#n {u} {α} a b → Eq#n {u} {α} b a
Eq:symm#n {u} {α} {a} {b} h
  = Eq:rec#zn {u} {α} {a} {λ (x$ : α) → λ (_ : Eq#n {u} {α} a x$) → Eq#n {u} {α} x$ a} (rfl#n {u} {α} {a}) {b} h

--def
#15 : {a : Nat} → {b : Nat} → #0 a b → #0 b a
#15 {a} {b} = Eq:symm#n {lone} {Nat} {a} {b}

--inductive 1 2->1 2 1
data HEq#z {α : Prop} : α → {β : Prop} → β → Prop where
  HEq:refl#z : (a : α) → HEq#z {α} a {α} a

--def
#46#z : Prop → Prop → Prop
#46#z = Eq#n {lone} {Prop}

--inductive 1 2->1 1 1
data Eq#z {α : Prop} : α → α → Prop where
  Eq:refl#z : (a : α) → Eq#z {α} a a

--def
cast#z : {α : Prop} → {β : Prop} → #46#z α β → α → β
cast#z {α} {β} h a = Eq:rec#zn {lone} {Prop} {α} {λ (x$ : Prop) → λ (_ : #46#z α x$) → x$} a {β} h

--def
#47#z : Prop
#47#z = (α : Prop) → (β : Prop) → (a : α) → (b : β) → HEq#z {α} a {β} b → (h : #46#z α β) → Eq#z {β} (cast#z {α} {β} h a) b

--def
#48#z : {a : Prop} → #46#z a a
#48#z {a} = rfl#n {lone} {Prop} {a}

--def
rfl#z : {α : Prop} → {a : α} → Eq#z {α} a a
rfl#z {α} {a} = Eq:refl#z {α} a

--recursor 2->1 2->3 1 1
HEq:rec#zz :
  {α : Prop} →
    {a$ : α} →
      {motive : {β : Prop} → (a$1 : β) → HEq#z {α} a$ {β} a$1 → Prop} →
        motive {α} a$ (HEq:refl#z {α} a$) → {β : Prop} → {a$1 : β} → (t : HEq#z {α} a$ {β} a$1) → motive {β} a$1 t
HEq:rec#zz {α} {a$} {motive} refl {_} {_} (HEq:refl#z a$) = refl

--theorem
eq-of-heq#z : {α : Prop} → {a : α} → {a' : α} → HEq#z {α} a {α} a' → Eq#z {α} a a'
eq-of-heq#z {α} {a} {a'} h
  = letFun#zz
    {#47#z}
    {λ (_ : #47#z) → Eq#z {α} (cast#z {α} {α} (#48#z {α}) a) a'}
    (λ (x$ : Prop) →
      λ (x$1 : Prop) →
        λ (x$2 : x$) →
          λ (x$3 : x$1) →
            λ (h₁ : HEq#z {x$} x$2 {x$1} x$3) →
              HEq:rec#zz
                {x$}
                {x$2}
                {λ {x$4 : Prop} →
                  λ (x$5 : x$4) → λ (_ : HEq#z {x$} x$2 {x$4} x$5) → (h# : #46#z x$ x$4) → Eq#z {x$4} (cast#z {x$} {x$4} h# x$2) x$5}
                (λ (x$4 : #46#z x$ x$) → rfl#z {x$} {cast#z {x$} {x$} x$4 x$2})
                {x$1}
                {x$3}
                h₁)
    (λ (this : #47#z) → this α α a a' h (#48#z {α}))

--recursor 2->1 1->2 1 1
Eq:rec#zz :
  {α : Prop} →
    {a$ : α} →
      {motive : (a$1 : α) → Eq#z {α} a$ a$1 → Prop} → motive a$ (Eq:refl#z {α} a$) → {a$1 : α} → (t : Eq#z {α} a$ a$1) → motive a$1 t
Eq:rec#zz {α} {a$} {motive} refl {_} (Eq:refl#z a$) = refl

--def
Eq:ndrec#zz : {α : Prop} → {a : α} → {motive : α → Prop} → motive a → {b : α} → Eq#z {α} a b → motive b
Eq:ndrec#zz {α} {a} {motive} m {b} h = Eq:rec#zz {α} {a} {λ (x$ : α) → λ (_ : Eq#z {α} a x$) → motive x$} m {b} h

--theorem
Eq:symm#z : {α : Prop} → {a : α} → {b : α} → Eq#z {α} a b → Eq#z {α} b a
Eq:symm#z {α} {a} {b} h = Eq:rec#zz {α} {a} {λ (x$ : α) → λ (_ : Eq#z {α} a x$) → Eq#z {α} x$ a} (rfl#z {α} {a}) {b} h

--recursor 1->1 1->1 1 2
Nat:le:rec :
  {n : Nat} →
    {motive : (a$ : Nat) → Nat:le n a$ → Prop} →
      motive n (Nat:le:refl {n}) →
        ({m : Nat} → (a$ : Nat:le n m) → motive m a$ → motive (Nat:succ m) (Nat:le:step {n} {m} a$)) →
          {a$ : Nat} → (t : Nat:le n a$) → motive a$ t
Nat:le:rec {n} {motive} refl _ {_} (Nat:le:refl) = refl
Nat:le:rec {n} {motive} refl step {_} (Nat:le:step {m} a$) = step {m} a$ (Nat:le:rec {n} {motive} refl step {m} a$)

--def
Nat:le:casesOn :
  {n : Nat} →
    {motive : (a$ : Nat) → Nat:le n a$ → Prop} →
      {a$ : Nat} →
        (t : Nat:le n a$) →
          motive n (Nat:le:refl {n}) → ({m : Nat} → (a$1 : Nat:le n m) → motive (Nat:succ m) (Nat:le:step {n} {m} a$1)) → motive a$ t
Nat:le:casesOn {n} {motive} {a$} t refl step
  = Nat:le:rec {n} {motive} refl (λ {m : Nat} → λ (a$1 : Nat:le n m) → λ (_ : motive m a$1) → step {m} a$1) {a$} t

--def
Nat:le-trans:match-1 :
  {n : Nat} →
    {m : Nat} →
      (motive : (k$ : Nat) → #31 n m → #31 m k$ → Prop) →
        (k$ : Nat) →
          (x$ : #31 n m) →
            (x$1 : #31 m k$) →
              ((h : #31 n m) → motive m h (Nat:le:refl {m})) →
                ((h₁ : #31 n m) → (m$ : Nat) → (h₂ : Nat:le m m$) → motive (Nat:succ m$) h₁ (Nat:le:step {m} {m$} h₂)) → motive k$ x$ x$1
Nat:le-trans:match-1 {n} {m} motive k$ x$ x$1 h-1 h-2
  = (λ (x$2 : Nat:le m k$) →
    Nat:le:casesOn
      {m}
      {λ (a$ : Nat) → λ (x : Nat:le m a$) → #0 k$ a$ → HEq#z {#31 m k$} x$1 {Nat:le m a$} x → motive k$ x$ x$1}
      {k$}
      x$2
      (λ (h$ : #0 k$ m) →
        #5
          {m}
          {λ (k$1 : Nat) → (x$3 : #31 m k$1) → HEq#z {#31 m k$1} x$3 {Nat:le m m} (Nat:le:refl {m}) → motive k$1 x$ x$3}
          (λ (x$3 : #31 m m) →
            λ (h$1 : HEq#z {#31 m m} x$3 {Nat:le m m} (Nat:le:refl {m})) →
              Eq:ndrec#zz
                {#31 m m}
                {Nat:le:refl {m}}
                {λ (x$4 : #31 m m) → motive m x$ x$4}
                (h-1 x$)
                {x$3}
                (Eq:symm#z {#31 m m} {x$3} {Nat:le:refl {m}} (eq-of-heq#z {#31 m m} {x$3} {Nat:le:refl {m}} h$1)))
          {k$}
          (#15 {k$} {m} h$)
          x$1)
      (λ {m$ : Nat} →
        λ (a$ : Nat:le m m$) →
          λ (h$ : #0 k$ (Nat:succ m$)) →
            #5
              {Nat:succ m$}
              {λ (k$1 : Nat) →
                (x$3 : #31 m k$1) → HEq#z {#31 m k$1} x$3 {Nat:le m (Nat:succ m$)} (Nat:le:step {m} {m$} a$) → motive k$1 x$ x$3}
              (λ (x$3 : #31 m (Nat:succ m$)) →
                λ (h$1 : HEq#z {#31 m (Nat:succ m$)} x$3 {Nat:le m (Nat:succ m$)} (Nat:le:step {m} {m$} a$)) →
                  Eq:ndrec#zz
                    {#31 m (Nat:succ m$)}
                    {Nat:le:step {m} {m$} a$}
                    {λ (x$4 : #31 m (Nat:succ m$)) → motive (Nat:succ m$) x$ x$4}
                    (h-2 x$ m$ a$)
                    {x$3}
                    (Eq:symm#z
                      {#31 m (Nat:succ m$)}
                      {x$3}
                      {Nat:le:step {m} {m$} a$}
                      (eq-of-heq#z {#31 m (Nat:succ m$)} {x$3} {Nat:le:step {m} {m$} a$} h$1)))
              {k$}
              (#15 {k$} {Nat:succ m$} h$)
              x$1))
    x$1
    (Eq:refl#n {lone} {Nat} k$)
    (HEq:refl#z {#31 m k$} x$1)

--theorem
Nat:le-trans : {n : Nat} → {m : Nat} → {k : Nat} → #31 n m → #31 m k → #31 n k
Nat:le-trans {n} {m} {k} x$ x$1
  = Nat:brecOn#z
    {λ (k# : Nat) → #31 n m → #31 m k# → #31 n k#}
    k
    (λ (k# : Nat) →
      λ (f : Nat:below#z {λ (k#1 : Nat) → #31 n m → #31 m k#1 → #31 n k#1} k#) →
        λ (x$2 : #31 n m) →
          λ (x$3 : #31 m k#) →
            Nat:le-trans:match-1
              {n}
              {m}
              (λ (k$ : Nat) → λ (_ : #31 n m) → λ (_ : #31 m k$) → Nat:below#z {λ (k#1 : Nat) → #31 n m → #31 m k#1 → #31 n k#1} k$ → #31 n k$)
              k#
              x$2
              x$3
              (λ (h : #31 n m) → λ (_ : Nat:below#z {λ (k#1 : Nat) → #31 n m → #31 m k#1 → #31 n k#1} m) → h)
              (λ (h₁ : #31 n m) →
                λ (m$ : Nat) →
                  λ (h₂ : Nat:le m m$) →
                    λ (x$4 : Nat:below#z {λ (k#1 : Nat) → #31 n m → #31 m k#1 → #31 n k#1} (Nat:succ m$)) →
                      Nat:le:step {n} {m$} (PProd#zn.fst {lone} x$4 h₁ h₂))
              f)
    x$
    x$1

--def
Unit : Set₁
Unit = PUnit#n {lone}

--def
#49#n : {u-1 : Level} → Type u-1
#49#n {u-1} = #7 → Set u-1

--def
Unit:unit : Unit
Unit:unit = PUnit:unit#n {lone}

--def
Nat:pow:match-1#n :
  {u-1 : Level} → (motive : #49#n {u-1}) → (x$ : #7) → (Unit → motive #4) → ((n : Nat) → motive (Nat:succ n)) → motive x$
Nat:pow:match-1#n {u-1} motive x$ h-1 h-2 = Nat:casesOn#n {u-1} {λ (x : #7) → motive x} x$ (h-1 Unit:unit) (λ (n$ : Nat) → h-2 n$)

--def
Nat:pred : #7 → Nat
Nat:pred x$ = Nat:pow:match-1#n {lone} (λ (_ : #7) → Nat) x$ (λ (_ : Unit) → #4) (λ (a : Nat) → a)

--def
#50 : Set₁
#50 = (x$ : Nat) → (x$1 : Nat) → #31 x$ x$1 → Prop

--def
#51 : Set₁
#51 = Nat → Prop

--def
#52 : #51
#52 = Nat:le #4

--def
#53 : {m : Nat} → #52 m → #52 (Nat:succ m)
#53 {m} = Nat:le:step {#4} {m}

--def
#54 : Prop
#54 = #34 Nat:zero

--def
#55 : #51
#55 = Nat:le Nat:zero

--def
#56 : Prop
#56 = #55 Nat:zero

--def
#57 : #56
#57 = Nat:le:refl {Nat:zero}

--def
#58 : {m : Nat} → #55 m → #55 (Nat:succ m)
#58 {m} = Nat:le:step {Nat:zero} {m}

--def
#59 :
  {motive : (a$ : Nat) → #55 a$ → Prop} →
    {a$ : Nat} → (t : #55 a$) → motive Nat:zero #57 → ({m : Nat} → (a$1 : #55 m) → motive (Nat:succ m) (#58 {m} a$1)) → motive a$ t
#59 {motive} {a$} = Nat:le:casesOn {Nat:zero} {motive} {a$}

--def
#60 : #54 → {β : Prop} → β → Prop
#60 = HEq#z {#54}

--def
#61 : Prop
#61 = #37 Nat:zero

--def
#62 : (a : Nat) → #0 a a
#62 = Eq:refl#n {lone} {Nat}

--def
#63 : #61
#63 = #62 Nat:zero

--recursor 0->0 0->0 1 2
Nat:rec#z : {motive : #43#z} → motive Nat:zero → ((n : Nat) → motive n → motive (Nat:succ n)) → (t : Nat) → motive t
Nat:rec#z {motive} zero _ (Nat:zero) = zero
Nat:rec#z {motive} zero succ (Nat:succ n) = succ n (Nat:rec#z {motive} zero succ n)

--def
Nat:casesOn#z : {motive : #43#z} → (t : Nat) → motive Nat:zero → ((n : Nat) → motive (Nat:succ n)) → motive t
Nat:casesOn#z {motive} t zero succ = Nat:rec#z {motive} zero (λ (n : Nat) → λ (_ : motive n) → succ n) t

--def
#64#z : Nat → Prop → (Nat → Prop) → Prop
#64#z = Nat:casesOn#n {lone} {λ (_ : Nat) → Prop}

--def
Nat:noConfusionType#z : Prop → Nat → Nat → Prop
Nat:noConfusionType#z P v1 v2
  = #64#z v1 (#64#z v2 (P → P) (λ (_ : Nat) → P)) (λ (n : Nat) → #64#z v2 P (λ (n# : Nat) → (#0 n n# → P) → P))

--def
Nat:noConfusion#z : {P : Prop} → {v1 : Nat} → {v2 : Nat} → #0 v1 v2 → Nat:noConfusionType#z P v1 v2
Nat:noConfusion#z {P} {v1} {v2} h12
  = Eq:ndrec#zn {lone}
    {Nat}
    {v1}
    {λ (a : Nat) → #0 v1 a → Nat:noConfusionType#z P v1 a}
    (λ (_ : #0 v1 v1) →
      Nat:casesOn#z
        {λ (v1# : Nat) → Nat:noConfusionType#z P v1# v1#}
        v1
        (λ (a : P) → a)
        (λ (n : Nat) → λ (a : #0 n n → P) → a (#62 n)))
    {v2}
    h12
    h12

--def
Nat:pred-le-pred:match-1 :
  (motive : #50) →
    (x$ : Nat) →
      (x$1 : Nat) →
        (x$2 : #31 x$ x$1) →
          ((n$ : Nat) → motive n$ n$ (Nat:le:refl {n$})) →
            ((n$ : Nat) → (h : #52 n$) → motive #4 (Nat:succ n$) (#53 {n$} h)) →
              ((n$ : Nat) →
                (n$1 : Nat) → (h : Nat:le (Nat:succ n$) n$1) → motive (Nat:succ n$) (Nat:succ n$1) (Nat:le:step {Nat:succ n$} {n$1} h)) →
                motive x$ x$1 x$2
Nat:pred-le-pred:match-1 motive x$ x$1 x$2 h-1 h-2 h-3
  = Nat:casesOn#z
    {λ (x : Nat) → (x$3 : #31 x x$1) → motive x x$1 x$3}
    x$
    (λ (x$3 : #34 x$1) →
      Nat:casesOn#z
        {λ (x : Nat) → (x$4 : #34 x) → motive Nat:zero x x$4}
        x$1
        (λ (x$4 : #54) →
          #59
            {λ (a$ : Nat) → λ (x : #55 a$) → #37 a$ → #60 x$4 {#55 a$} x → motive Nat:zero Nat:zero x$4}
            {Nat:zero}
            x$4
            (λ (_ : #61) →
              λ (h$ : #60 x$4 {#56} #57) →
                Eq:ndrec#zz
                  {#54}
                  {#57}
                  {λ (x$5 : #54) → motive Nat:zero Nat:zero x$5}
                  (h-1 Nat:zero)
                  {x$4}
                  (Eq:symm#z {#54} {x$4} {#57} (eq-of-heq#z {#54} {x$4} {#57} h$)))
            (λ {m$ : Nat} →
              λ (a$ : #55 m$) →
                λ (h$ : #37 (Nat:succ m$)) →
                  Nat:noConfusion#z
                    {#60 x$4 {#55 (Nat:succ m$)} (#58 {m$} a$) → motive Nat:zero Nat:zero x$4}
                    {Nat:zero}
                    {Nat:succ m$}
                    h$)
            #63
            (HEq:refl#z {#54} x$4))
        (λ (n$ : Nat) →
          λ (x$4 : #34 (Nat:succ n$)) →
            #59
              {λ (a$ : Nat) →
                λ (x : #55 a$) → #0 (Nat:succ n$) a$ → HEq#z {#34 (Nat:succ n$)} x$4 {#55 a$} x → motive Nat:zero (Nat:succ n$) x$4}
              {Nat:succ n$}
              x$4
              (λ (h$ : #0 (Nat:succ n$) Nat:zero) →
                Nat:noConfusion#z
                  {HEq#z {#34 (Nat:succ n$)} x$4 {#56} #57 → motive Nat:zero (Nat:succ n$) x$4}
                  {Nat:succ n$}
                  {Nat:zero}
                  h$)
              (λ {m$ : Nat} →
                λ (a$ : #55 m$) →
                  λ (h$ : #0 (Nat:succ n$) (Nat:succ m$)) →
                    Nat:noConfusion#z
                      {HEq#z {#34 (Nat:succ n$)} x$4 {#55 (Nat:succ m$)} (#58 {m$} a$) → motive Nat:zero (Nat:succ n$) x$4}
                      {Nat:succ n$}
                      {Nat:succ m$}
                      h$
                      (λ (n-eq$ : #0 n$ m$) →
                        #5
                          {n$}
                          {λ (m$1 : Nat) →
                            (a$1 : #55 m$1) →
                              HEq#z {#34 (Nat:succ n$)} x$4 {#55 (Nat:succ m$1)} (#58 {m$1} a$1) → motive Nat:zero (Nat:succ n$) x$4}
                          (λ (a$1 : #55 n$) →
                            λ (h$1 : HEq#z {#34 (Nat:succ n$)} x$4 {#55 (Nat:succ n$)} (#58 {n$} a$1)) →
                              Eq:ndrec#zz
                                {#34 (Nat:succ n$)}
                                {#58 {n$} a$1}
                                {λ (x$5 : #34 (Nat:succ n$)) → motive Nat:zero (Nat:succ n$) x$5}
                                (h-2 n$ a$1)
                                {x$4}
                                (Eq:symm#z
                                  {#34 (Nat:succ n$)}
                                  {x$4}
                                  {#58 {n$} a$1}
                                  (eq-of-heq#z {#34 (Nat:succ n$)} {x$4} {#58 {n$} a$1} h$1)))
                          {m$}
                          n-eq$
                          a$))
              (#62 (Nat:succ n$))
              (HEq:refl#z {#34 (Nat:succ n$)} x$4))
        x$3)
    (λ (n$ : Nat) →
      λ (x$3 : #31 (Nat:succ n$) x$1) →
        Nat:casesOn#z
          {λ (x : Nat) → (x$4 : #31 (Nat:succ n$) x) → motive (Nat:succ n$) x x$4}
          x$1
          (λ (x$4 : #31 (Nat:succ n$) Nat:zero) →
            Nat:le:casesOn
              {Nat:succ n$}
              {λ (a$ : Nat) →
                λ (x : Nat:le (Nat:succ n$) a$) →
                  #37 a$ → HEq#z {#31 (Nat:succ n$) Nat:zero} x$4 {Nat:le (Nat:succ n$) a$} x → motive (Nat:succ n$) Nat:zero x$4}
              {Nat:zero}
              x$4
              (λ (h$ : #37 (Nat:succ n$)) →
                Nat:noConfusion#z
                  {HEq#z {#31 (Nat:succ n$) Nat:zero} x$4 {Nat:le (Nat:succ n$) (Nat:succ n$)} (Nat:le:refl {Nat:succ n$}) →
                    motive (Nat:succ n$) Nat:zero x$4}
                  {Nat:zero}
                  {Nat:succ n$}
                  h$)
              (λ {m$ : Nat} →
                λ (a$ : Nat:le (Nat:succ n$) m$) →
                  λ (h$ : #37 (Nat:succ m$)) →
                    Nat:noConfusion#z
                      {HEq#z
                        {#31 (Nat:succ n$) Nat:zero}
                        x$4
                        {Nat:le (Nat:succ n$) (Nat:succ m$)}
                        (Nat:le:step {Nat:succ n$} {m$} a$) →
                        motive (Nat:succ n$) Nat:zero x$4}
                      {Nat:zero}
                      {Nat:succ m$}
                      h$)
              #63
              (HEq:refl#z {#31 (Nat:succ n$) Nat:zero} x$4))
          (λ (n$1 : Nat) →
            λ (x$4 : #31 (Nat:succ n$) (Nat:succ n$1)) →
              Nat:le:casesOn
                {Nat:succ n$}
                {λ (a$ : Nat) →
                  λ (x : Nat:le (Nat:succ n$) a$) →
                    #0 (Nat:succ n$1) a$ →
                      HEq#z {#31 (Nat:succ n$) (Nat:succ n$1)} x$4 {Nat:le (Nat:succ n$) a$} x → motive (Nat:succ n$) (Nat:succ n$1) x$4}
                {Nat:succ n$1}
                x$4
                (λ (h$ : #0 (Nat:succ n$1) (Nat:succ n$)) →
                  Nat:noConfusion#z
                    {HEq#z {#31 (Nat:succ n$) (Nat:succ n$1)} x$4 {Nat:le (Nat:succ n$) (Nat:succ n$)} (Nat:le:refl {Nat:succ n$}) →
                      motive (Nat:succ n$) (Nat:succ n$1) x$4}
                    {Nat:succ n$1}
                    {Nat:succ n$}
                    h$
                    (λ (n-eq$ : #0 n$1 n$) →
                      #5
                        {n$}
                        {λ (n$2 : Nat) →
                          (x$5 : #31 (Nat:succ n$) (Nat:succ n$2)) →
                            HEq#z
                              {#31 (Nat:succ n$) (Nat:succ n$2)}
                              x$5
                              {Nat:le (Nat:succ n$) (Nat:succ n$)}
                              (Nat:le:refl {Nat:succ n$}) →
                              motive (Nat:succ n$) (Nat:succ n$2) x$5}
                        (λ (x$5 : #31 (Nat:succ n$) (Nat:succ n$)) →
                          λ
                            (h$1 :
                              HEq#z
                                {#31 (Nat:succ n$) (Nat:succ n$)}
                                x$5
                                {Nat:le (Nat:succ n$) (Nat:succ n$)}
                                (Nat:le:refl {Nat:succ n$})) →
                            Eq:ndrec#zz
                              {#31 (Nat:succ n$) (Nat:succ n$)}
                              {Nat:le:refl {Nat:succ n$}}
                              {λ (x$6 : #31 (Nat:succ n$) (Nat:succ n$)) → motive (Nat:succ n$) (Nat:succ n$) x$6}
                              (h-1 (Nat:succ n$))
                              {x$5}
                              (Eq:symm#z
                                {#31 (Nat:succ n$) (Nat:succ n$)}
                                {x$5}
                                {Nat:le:refl {Nat:succ n$}}
                                (eq-of-heq#z {#31 (Nat:succ n$) (Nat:succ n$)} {x$5} {Nat:le:refl {Nat:succ n$}} h$1)))
                        {n$1}
                        (#15 {n$1} {n$} n-eq$)
                        x$4))
                (λ {m$ : Nat} →
                  λ (a$ : Nat:le (Nat:succ n$) m$) →
                    λ (h$ : #0 (Nat:succ n$1) (Nat:succ m$)) →
                      Nat:noConfusion#z
                        {HEq#z
                          {#31 (Nat:succ n$) (Nat:succ n$1)}
                          x$4
                          {Nat:le (Nat:succ n$) (Nat:succ m$)}
                          (Nat:le:step {Nat:succ n$} {m$} a$) →
                          motive (Nat:succ n$) (Nat:succ n$1) x$4}
                        {Nat:succ n$1}
                        {Nat:succ m$}
                        h$
                        (λ (n-eq$ : #0 n$1 m$) →
                          #5
                            {n$1}
                            {λ (m$1 : Nat) →
                              (a$1 : Nat:le (Nat:succ n$) m$1) →
                                HEq#z
                                  {#31 (Nat:succ n$) (Nat:succ n$1)}
                                  x$4
                                  {Nat:le (Nat:succ n$) (Nat:succ m$1)}
                                  (Nat:le:step {Nat:succ n$} {m$1} a$1) →
                                  motive (Nat:succ n$) (Nat:succ n$1) x$4}
                            (λ (a$1 : Nat:le (Nat:succ n$) n$1) →
                              λ
                                (h$1 :
                                  HEq#z
                                    {#31 (Nat:succ n$) (Nat:succ n$1)}
                                    x$4
                                    {Nat:le (Nat:succ n$) (Nat:succ n$1)}
                                    (Nat:le:step {Nat:succ n$} {n$1} a$1)) →
                                Eq:ndrec#zz
                                  {#31 (Nat:succ n$) (Nat:succ n$1)}
                                  {Nat:le:step {Nat:succ n$} {n$1} a$1}
                                  {λ (x$5 : #31 (Nat:succ n$) (Nat:succ n$1)) → motive (Nat:succ n$) (Nat:succ n$1) x$5}
                                  (h-3 n$ n$1 a$1)
                                  {x$4}
                                  (Eq:symm#z
                                    {#31 (Nat:succ n$) (Nat:succ n$1)}
                                    {x$4}
                                    {Nat:le:step {Nat:succ n$} {n$1} a$1}
                                    (eq-of-heq#z {#31 (Nat:succ n$) (Nat:succ n$1)} {x$4} {Nat:le:step {Nat:succ n$} {n$1} a$1} h$1)))
                            {m$}
                            n-eq$
                            a$))
                (#62 (Nat:succ n$1))
                (HEq:refl#z {#31 (Nat:succ n$) (Nat:succ n$1)} x$4))
          x$3)
    x$2

--theorem
Nat:pred-le-pred : {n : Nat} → {m : Nat} → #31 n m → #31 (Nat:pred n) (Nat:pred m)
Nat:pred-le-pred {x$} {x$1} x$2
  = Nat:pred-le-pred:match-1
    (λ (x$3 : Nat) → λ (x$4 : Nat) → λ (_ : #31 x$3 x$4) → #31 (Nat:pred x$3) (Nat:pred x$4))
    x$
    x$1
    x$2
    (λ (n$ : Nat) → Nat:le:refl {Nat:pred n$})
    (λ (n$ : Nat) → λ (h : Nat:le #4 n$) → h)
    (λ (n$ : Nat) →
      λ (n$1 : Nat) →
        λ (h : Nat:le (Nat:succ n$) n$1) →
          Nat:le-trans
            {Nat:pred (Nat:succ n$)}
            {Nat:succ (Nat:pred (Nat:succ n$))}
            {Nat:pred (Nat:succ n$1)}
            (Nat:le-succ (Nat:pred (Nat:succ n$)))
            h)

--theorem
Nat:le-of-succ-le-succ : {n : Nat} → {m : Nat} → #31 (Nat:succ n) (Nat:succ m) → #31 n m
Nat:le-of-succ-le-succ {n} {m} = Nat:pred-le-pred {Nat:succ n} {Nat:succ m}

--def
#65 : Prop
#65 = #31 (Nat:succ #4) #4

--def
#66 : Set₁
#66 = #65 → Prop

--def
#67 : Nat
#67 = Nat:succ #4

--def
#68 : #51
#68 = Nat:le #67

--def
#69 : #36
#69 = #0 #4

--def
#70 : #65 → {β : Prop} → β → Prop
#70 = HEq#z {#65}

--def
Nat:not-succ-le-zero:match-1 : (motive : #66) → (a$ : #65) → motive a$
Nat:not-succ-le-zero:match-1 motive a$
  = (λ (a$1 : #68 #4) →
    Nat:le:casesOn
      {#67}
      {λ (a$2 : Nat) → λ (x : #68 a$2) → #69 a$2 → #70 a$ {#68 a$2} x → motive a$}
      {#4}
      a$1
      (λ (h$ : #69 #67) → Nat:noConfusion#z {#70 a$ {#68 #67} (Nat:le:refl {#67}) → motive a$} {#4} {#67} h$)
      (λ {m$ : Nat} →
        λ (a$2 : #68 m$) →
          λ (h$ : #69 (Nat:succ m$)) →
            Nat:noConfusion#z {#70 a$ {#68 (Nat:succ m$)} (Nat:le:step {#67} {m$} a$2) → motive a$} {#4} {Nat:succ m$} h$))
    a$
    (#62 #4)
    (HEq:refl#z {#65} a$)

--def
Nat:not-succ-le-zero:match-2 :
  (n$ : Nat) → (motive : #31 (Nat:succ (Nat:succ n$)) #4 → Prop) → (a$ : #31 (Nat:succ (Nat:succ n$)) #4) → motive a$
Nat:not-succ-le-zero:match-2 n$ motive a$
  = (λ (a$1 : Nat:le (Nat:succ (Nat:succ n$)) #4) →
    Nat:le:casesOn
      {Nat:succ (Nat:succ n$)}
      {λ (a$2 : Nat) →
        λ (x : Nat:le (Nat:succ (Nat:succ n$)) a$2) →
          #69 a$2 → HEq#z {#31 (Nat:succ (Nat:succ n$)) #4} a$ {Nat:le (Nat:succ (Nat:succ n$)) a$2} x → motive a$}
      {#4}
      a$1
      (λ (h$ : #69 (Nat:succ (Nat:succ n$))) →
        Nat:noConfusion#z
          {HEq#z
            {#31 (Nat:succ (Nat:succ n$)) #4}
            a$
            {Nat:le (Nat:succ (Nat:succ n$)) (Nat:succ (Nat:succ n$))}
            (Nat:le:refl {Nat:succ (Nat:succ n$)}) →
            motive a$}
          {#4}
          {Nat:succ (Nat:succ n$)}
          h$)
      (λ {m$ : Nat} →
        λ (a$2 : Nat:le (Nat:succ (Nat:succ n$)) m$) →
          λ (h$ : #69 (Nat:succ m$)) →
            Nat:noConfusion#z
              {HEq#z
                {#31 (Nat:succ (Nat:succ n$)) #4}
                a$
                {Nat:le (Nat:succ (Nat:succ n$)) (Nat:succ m$)}
                (Nat:le:step {Nat:succ (Nat:succ n$)} {m$} a$2) →
                motive a$}
              {#4}
              {Nat:succ m$}
              h$))
    a$
    (#62 #4)
    (HEq:refl#z {#31 (Nat:succ (Nat:succ n$)) #4} a$)

--def
#71 : Set₁
#71 = Nat → Prop

--def
Nat:not-succ-le-zero:match-3 : (motive : #71) → (x$ : Nat) → (Unit → motive #4) → ((n$ : Nat) → motive (Nat:succ n$)) → motive x$
Nat:not-succ-le-zero:match-3 motive x$ h-1 h-2 = Nat:casesOn#z {λ (x : Nat) → motive x} x$ (h-1 Unit:unit) (λ (n$ : Nat) → h-2 n$)

--theorem
Nat:not-succ-le-zero : (n : Nat) → #31 (Nat:succ n) #4 → False
Nat:not-succ-le-zero x$
  = Nat:not-succ-le-zero:match-3
    (λ (x$1 : Nat) → #31 (Nat:succ x$1) #4 → False)
    x$
    (λ (_ : Unit) → λ (a$ : #65) → Nat:not-succ-le-zero:match-1 (λ (_ : #65) → False) a$)
    (λ (n$ : Nat) →
      λ (a$ : #31 (Nat:succ (Nat:succ n$)) #4) → Nat:not-succ-le-zero:match-2 n$ (λ (_ : #31 (Nat:succ (Nat:succ n$)) #4) → False) a$)

--def
Nat:succ-le-succ:match-1 :
  {n : Nat} →
    (motive : (m$ : Nat) → #31 n m$ → Prop) →
      (m$ : Nat) →
        (x$ : #31 n m$) →
          (Unit → motive n (Nat:le:refl {n})) →
            ((m$1 : Nat) → (h : Nat:le n m$1) → motive (Nat:succ m$1) (Nat:le:step {n} {m$1} h)) → motive m$ x$
Nat:succ-le-succ:match-1 {n} motive m$ x$ h-1 h-2
  = (λ (x$1 : Nat:le n m$) →
    Nat:le:casesOn
      {n}
      {λ (a$ : Nat) → λ (x : Nat:le n a$) → #0 m$ a$ → HEq#z {#31 n m$} x$ {Nat:le n a$} x → motive m$ x$}
      {m$}
      x$1
      (λ (h$ : #0 m$ n) →
        #5
          {n}
          {λ (m$1 : Nat) → (x$2 : #31 n m$1) → HEq#z {#31 n m$1} x$2 {Nat:le n n} (Nat:le:refl {n}) → motive m$1 x$2}
          (λ (x$2 : #31 n n) →
            λ (h$1 : HEq#z {#31 n n} x$2 {Nat:le n n} (Nat:le:refl {n})) →
              Eq:ndrec#zz
                {#31 n n}
                {Nat:le:refl {n}}
                {λ (x$3 : #31 n n) → motive n x$3}
                (h-1 Unit:unit)
                {x$2}
                (Eq:symm#z {#31 n n} {x$2} {Nat:le:refl {n}} (eq-of-heq#z {#31 n n} {x$2} {Nat:le:refl {n}} h$1)))
          {m$}
          (#15 {m$} {n} h$)
          x$)
      (λ {m$1 : Nat} →
        λ (a$ : Nat:le n m$1) →
          λ (h$ : #0 m$ (Nat:succ m$1)) →
            #5
              {Nat:succ m$1}
              {λ (m$2 : Nat) →
                (x$2 : #31 n m$2) → HEq#z {#31 n m$2} x$2 {Nat:le n (Nat:succ m$1)} (Nat:le:step {n} {m$1} a$) → motive m$2 x$2}
              (λ (x$2 : #31 n (Nat:succ m$1)) →
                λ (h$1 : HEq#z {#31 n (Nat:succ m$1)} x$2 {Nat:le n (Nat:succ m$1)} (Nat:le:step {n} {m$1} a$)) →
                  Eq:ndrec#zz
                    {#31 n (Nat:succ m$1)}
                    {Nat:le:step {n} {m$1} a$}
                    {λ (x$3 : #31 n (Nat:succ m$1)) → motive (Nat:succ m$1) x$3}
                    (h-2 m$1 a$)
                    {x$2}
                    (Eq:symm#z
                      {#31 n (Nat:succ m$1)}
                      {x$2}
                      {Nat:le:step {n} {m$1} a$}
                      (eq-of-heq#z {#31 n (Nat:succ m$1)} {x$2} {Nat:le:step {n} {m$1} a$} h$1)))
              {m$}
              (#15 {m$} {Nat:succ m$1} h$)
              x$))
    x$
    (#62 m$)
    (HEq:refl#z {#31 n m$} x$)

--theorem
Nat:succ-le-succ : {n : Nat} → {m : Nat} → #31 n m → #31 (Nat:succ n) (Nat:succ m)
Nat:succ-le-succ {n} {m} x$
  = Nat:brecOn#z
    {λ (m# : Nat) → #31 n m# → #31 (Nat:succ n) (Nat:succ m#)}
    m
    (λ (m# : Nat) →
      λ (f : Nat:below#z {λ (m#1 : Nat) → #31 n m#1 → #31 (Nat:succ n) (Nat:succ m#1)} m#) →
        λ (x$1 : #31 n m#) →
          Nat:succ-le-succ:match-1
            {n}
            (λ (m$ : Nat) →
              λ (_ : #31 n m$) →
                Nat:below#z {λ (m#1 : Nat) → #31 n m#1 → #31 (Nat:succ n) (Nat:succ m#1)} m$ → #31 (Nat:succ n) (Nat:succ m$))
            m#
            x$1
            (λ (_ : Unit) → λ (_ : Nat:below#z {λ (m#1 : Nat) → #31 n m#1 → #31 (Nat:succ n) (Nat:succ m#1)} n) → Nat:le:refl {Nat:succ n})
            (λ (m$ : Nat) →
              λ (h : Nat:le n m$) →
                λ (x$2 : Nat:below#z {λ (m#1 : Nat) → #31 n m#1 → #31 (Nat:succ n) (Nat:succ m#1)} (Nat:succ m$)) →
                  Nat:le:step {Nat:succ n} {#16 m$ #17} (PProd#zn.fst {lone} x$2 h))
            f)
    x$

--def
#72 : #30
#72 = #31 #4

--def
#73 : Nat → Prop
#73 x$ = #72 x$

--def
#74 : Nat → Set₁
#74 = Nat:below#z {#73}

--def
#75 : Set₁
#75 = Nat → Prop

--def
Nat:zero-le:match-1 : (motive : #75) → (x$ : Nat) → (Unit → motive Nat:zero) → ((n : Nat) → motive (Nat:succ n)) → motive x$
Nat:zero-le:match-1 motive x$ h-1 h-2 = Nat:casesOn#z {λ (x : Nat) → motive x} x$ (h-1 Unit:unit) (λ (n$ : Nat) → h-2 n$)

--theorem
Nat:zero-le : (n : Nat) → #72 n
Nat:zero-le x$
  = Nat:brecOn#z
    {#73}
    x$
    (λ (x$1 : Nat) →
      λ (f : #74 x$1) →
        Nat:zero-le:match-1
          (λ (x$2 : Nat) → #74 x$2 → #72 x$2)
          x$1
          (λ (_ : Unit) → λ (_ : #74 Nat:zero) → Nat:le:refl {#4})
          (λ (n : Nat) → λ (x$2 : #74 (Nat:succ n)) → #53 {n} (PProd#zn.fst {lone} x$2))
          f)

--recursor 2->2 0->0 1 2
Or:rec :
  {a : Prop} →
    {b : Prop} →
      {motive : Or a b → Prop} →
        ((h : a) → motive (Or:inl {a} {b} h)) → ((h : b) → motive (Or:inr {a} {b} h)) → (t : Or a b) → motive t
Or:rec {a} {b} {motive} inl _ (Or:inl h) = inl h
Or:rec {a} {b} {motive} _ inr (Or:inr h) = inr h

--def
Or:casesOn :
  {a : Prop} →
    {b : Prop} →
      {motive : Or a b → Prop} →
        (t : Or a b) → ((h : a) → motive (Or:inl {a} {b} h)) → ((h : b) → motive (Or:inr {a} {b} h)) → motive t
Or:casesOn {a} {b} {motive} t inl inr = Or:rec {a} {b} {motive} (λ (h : a) → inl h) (λ (h : b) → inr h) t

--def
Nat:eq-or-lt-of-le:match-1 :
  (n : Nat) →
    (m : Nat) →
      (motive : Or (#0 n m) (#26 n m) → Prop) →
        (x$ : Or (#0 n m) (#26 n m)) →
          ((h : #0 n m) → motive (Or:inl {#0 n m} {#26 n m} h)) → ((h : #26 n m) → motive (Or:inr {#0 n m} {#26 n m} h)) → motive x$
Nat:eq-or-lt-of-le:match-1 n m motive x$ h-1 h-2
  = Or:casesOn
    {#0 n m}
    {#26 n m}
    {λ (x : Or (#0 n m) (#26 n m)) → motive x}
    x$
    (λ (h$ : #0 n m) → h-1 h$)
    (λ (h$ : #26 n m) → h-2 h$)

--def
#76 : Set₁
#76 = (x$ : Nat) → (x$1 : Nat) → #31 x$ x$1 → Prop

--def
Nat:eq-or-lt-of-le:match-2 :
  (motive : #76) →
    (x$ : Nat) →
      (x$1 : Nat) →
        (x$2 : #31 x$ x$1) →
          ((x$3 : #54) → motive Nat:zero Nat:zero x$3) →
            ((n$ : Nat) → (x$3 : #34 (Nat:succ n$)) → motive Nat:zero (Nat:succ n$) x$3) →
              ((n$ : Nat) → (h : #31 (Nat:succ n$) Nat:zero) → motive (Nat:succ n$) Nat:zero h) →
                ((n : Nat) → (m : Nat) → (h : #31 (Nat:succ n) (Nat:succ m)) → motive (Nat:succ n) (Nat:succ m) h) → motive x$ x$1 x$2
Nat:eq-or-lt-of-le:match-2 motive x$ x$1 x$2 h-1 h-2 h-3 h-4
  = Nat:casesOn#z
    {λ (x : Nat) → (x$3 : #31 x x$1) → motive x x$1 x$3}
    x$
    (λ (x$3 : #34 x$1) →
      Nat:casesOn#z
        {λ (x : Nat) → (x$4 : #34 x) → motive Nat:zero x x$4}
        x$1
        (λ (x$4 : #54) → h-1 x$4)
        (λ (n$ : Nat) → λ (x$4 : #34 (Nat:succ n$)) → h-2 n$ x$4)
        x$3)
    (λ (n$ : Nat) →
      λ (x$3 : #31 (Nat:succ n$) x$1) →
        Nat:casesOn#z
          {λ (x : Nat) → (x$4 : #31 (Nat:succ n$) x) → motive (Nat:succ n$) x x$4}
          x$1
          (λ (x$4 : #31 (Nat:succ n$) Nat:zero) → h-3 n$ x$4)
          (λ (n$1 : Nat) → λ (x$4 : #31 (Nat:succ n$) (Nat:succ n$1)) → h-4 n$ n$1 x$4)
          x$3)
    x$2

--theorem
Nat:eq-or-lt-of-le : {n : Nat} → {m : Nat} → #31 n m → Or (#0 n m) (#26 n m)
Nat:eq-or-lt-of-le {x$} {x$1} x$2
  = Nat:brecOn#z
    {#32}
    x$
    (λ (x$3 : Nat) →
      λ (f : #33 x$3) →
        λ (x$4 : Nat) →
          λ (x$5 : #31 x$3 x$4) →
            Nat:eq-or-lt-of-le:match-2
              (λ (x$6 : Nat) → λ (x$7 : Nat) → λ (_ : #31 x$6 x$7) → #33 x$6 → Or (#0 x$6 x$7) (#26 x$6 x$7))
              x$3
              x$4
              x$5
              (λ (_ : #34 Nat:zero) → λ (_ : #35) → Or:inl {#37 Nat:zero} {#39 Nat:zero} (#40 {Nat:zero}))
              (λ (n$ : Nat) →
                λ (_ : #34 (Nat:succ n$)) →
                  λ (_ : #35) → Or:inr {#37 (Nat:succ n$)} {#39 (Nat:succ n$)} (Nat:succ-le-succ {Nat:zero} {n$} (Nat:zero-le n$)))
              (λ (n$ : Nat) →
                λ (h : #31 (Nat:succ n$) Nat:zero) →
                  λ (_ : #33 (Nat:succ n$)) →
                    absurd#z
                      {#31 (Nat:succ n$) Nat:zero}
                      {Or (#0 (Nat:succ n$) Nat:zero) (#26 (Nat:succ n$) Nat:zero)}
                      h
                      (Nat:not-succ-le-zero n$))
              (λ (n : Nat) →
                λ (m : Nat) →
                  λ (h : #31 (Nat:succ n) (Nat:succ m)) →
                    λ (x$6 : #33 (Nat:succ n)) →
                      letFun#zz
                        {#31 n m}
                        {λ (_ : #31 n m) → Or (#0 (Nat:succ n) (Nat:succ m)) (#26 (Nat:succ n) (Nat:succ m))}
                        (Nat:le-of-succ-le-succ {n} {m} h)
                        (λ (this : #31 n m) →
                          Nat:eq-or-lt-of-le:match-1
                            n
                            m
                            (λ (_ : Or (#0 n m) (#26 n m)) → Or (#0 (Nat:succ n) (Nat:succ m)) (#26 (Nat:succ n) (Nat:succ m)))
                            (PProd#zn.fst {lone} x$6 m this)
                            (λ (h# : #0 n m) →
                              Or:inl
                                {#0 (Nat:succ n) (Nat:succ m)}
                                {#26 (Nat:succ n) (Nat:succ m)}
                                (Eq:rec#zn {lone}
                                  {Nat}
                                  {n}
                                  {λ (x$7 : Nat) → λ (_ : #0 n x$7) → #0 (Nat:succ n) (Nat:succ x$7)}
                                  (#40 {Nat:succ n})
                                  {m}
                                  h#))
                            (λ (h# : #26 n m) →
                              Or:inr
                                {#0 (Nat:succ n) (Nat:succ m)}
                                {#26 (Nat:succ n) (Nat:succ m)}
                                (Nat:succ-le-succ {#16 n #17} {m} h#))))
              f)
    x$1
    x$2

--theorem
Nat:not-lt-zero : (n : Nat) → Not (#26 n #4)
Nat:not-lt-zero n = Nat:not-succ-le-zero n

--def
#77#z : Set₁
#77#z = Nat → Prop

--def
Nat:recAux#z : {motive : #77#z} → motive #4 → ((n : Nat) → motive n → motive (#16 n #17)) → (t : Nat) → motive t
Nat:recAux#z {motive} zero succ t = Nat:rec#z {λ (x$ : Nat) → motive x$} zero succ t

--def
Nat:lt-wfRel:match-1 :
  (n : Nat) →
    (m : Nat) →
      (motive : Or (#0 m n) (#26 m n) → Prop) →
        (this$ : Or (#0 m n) (#26 m n)) →
          ((e : #0 m n) → motive (Or:inl {#0 m n} {#26 m n} e)) → ((e : #26 m n) → motive (Or:inr {#0 m n} {#26 m n} e)) → motive this$
Nat:lt-wfRel:match-1 n m motive this$ h-1 h-2
  = Or:casesOn
    {#0 m n}
    {#26 m n}
    {λ (x : Or (#0 m n) (#26 m n)) → motive x}
    this$
    (λ (h$ : #0 m n) → h-1 h$)
    (λ (h$ : #26 m n) → h-2 h$)

--theorem
Nat:lt-wfRel:proof-1 : WellFounded#n {lone} {Nat} #27
Nat:lt-wfRel:proof-1
  = WellFounded:intro#n {lone}
    {Nat}
    {#27}
    (λ (n : Nat) →
      Nat:recAux#z
        {λ (n# : Nat) → #28 n#}
        (#29 #4 (λ (y$ : Nat) → λ (h : #26 y$ #4) → absurd#z {#26 y$ #4} {#28 y$} h (Nat:not-lt-zero y$)))
        (λ (n# : Nat) →
          λ (ih : #28 n#) →
            #29
              (Nat:succ n#)
              (λ (m : Nat) →
                λ (h : #26 m (Nat:succ n#)) →
                  letFun#zz
                    {Or (#0 m n#) (#26 m n#)}
                    {λ (_ : Or (#0 m n#) (#26 m n#)) → #28 m}
                    (Nat:eq-or-lt-of-le {m} {n#} (Nat:le-of-succ-le-succ {m} {n#} h))
                    (λ (this : Or (#0 m n#) (#26 m n#)) →
                      Nat:lt-wfRel:match-1
                        n#
                        m
                        (λ (_ : Or (#0 m n#) (#26 m n#)) → #28 m)
                        this
                        (λ (e : #0 m n#) →
                          #5
                            {m}
                            {λ (n#1 : Nat) → #28 n#1 → #26 m (Nat:succ n#1) → Or (#0 m n#1) (#26 m n#1) → #28 m}
                            (λ (ih# : #28 m) → λ (_ : #26 m (Nat:succ m)) → λ (_ : Or (#0 m m) (#26 m m)) → ih#)
                            {n#}
                            e
                            ih
                            h
                            this)
                        (λ (e : #26 m n#) → Acc:inv#n {lone} {Nat} {#27} {n#} {m} ih e))))
        n)

--def
Nat:lt-wfRel : WellFoundedRelation#n {lone} Nat
Nat:lt-wfRel
  = WellFoundedRelation:mk#n {lone}
    {Nat}
    (λ (x1$ : Nat) → λ (x2$ : Nat) → LT:lt {lzero} {Nat} {{instLTNat}} x1$ x2$)
    Nat:lt-wfRel:proof-1

--def
measure#n : {u : Level} → {α : Set u} → (α → Nat) → WellFoundedRelation#n {u} α
measure#n {u} {α} f = invImage#nn {u} {lone} {α} {Nat} f Nat:lt-wfRel

--def
SizeOf:sizeOf#n : {u : Level} → {α : Set u} → {{SizeOf#n {u} α}} → α → Nat
SizeOf:sizeOf#n {u} {α} {{self}} = SizeOf#n.sizeOf {u} self

--def
sizeOfWFRel#n : {u : Level} → {α : Set u} → {{SizeOf#n {u} α}} → WellFoundedRelation#n {u} α
sizeOfWFRel#n {u} {α} {{inst$}} = measure#n {u} {α} (SizeOf:sizeOf#n {u} {α} {{inst$}})

--def
instWellFoundedRelationOfSizeOf#n : {u-1 : Level} → {α : Set u-1} → {{SizeOf#n {u-1} α}} → WellFoundedRelation#n {u-1} α
instWellFoundedRelationOfSizeOf#n {u-1} {α} {{inst$}} = sizeOfWFRel#n {u-1} {α} {{inst$}}

--def
#24 : #21 → #21 → Prop
#24
  = WellFoundedRelation#n.rel {lone}
    (invImage#nn {lone} {lone}
      {#21}
      {#7}
      (λ (x$ : #21) → #23 {λ (_ : #21) → #7} x$ (λ (m : #7) → λ (_ : #7) → m))
      (instWellFoundedRelationOfSizeOf#n {lone} {#7} {{instSizeOfNat}}))

--def
#25 : #7 → #7 → Prop
#25 = Eq#n {lone} {#7}

--inductive 0 1->1 0 1
data Decidable (p : Prop) : Set₁ where
  Decidable:isFalse : Not p → Decidable p
  Decidable:isTrue : p → Decidable p

--recursor 1->1 0->0 1 2
Decidable:rec#n :
  {u : Level} →
    {p : Prop} →
      {motive : Decidable p → Set u} →
        ((h : Not p) → motive (Decidable:isFalse {p} h)) → ((h : p) → motive (Decidable:isTrue {p} h)) → (t : Decidable p) → motive t
Decidable:rec#n {u} {p} {motive} isFalse _ (Decidable:isFalse h) = isFalse h
Decidable:rec#n {u} {p} {motive} _ isTrue (Decidable:isTrue h) = isTrue h

--def
Decidable:casesOn#n :
  {u : Level} →
    {p : Prop} →
      {motive : Decidable p → Set u} →
        (t : Decidable p) → ((h : Not p) → motive (Decidable:isFalse {p} h)) → ((h : p) → motive (Decidable:isTrue {p} h)) → motive t
Decidable:casesOn#n {u} {p} {motive} t isFalse isTrue
  = Decidable:rec#n {u} {p} {motive} (λ (h : Not p) → isFalse h) (λ (h : p) → isTrue h) t

--def
dite#n : {u : Level} → {α : Set u} → (c : Prop) → {{Decidable c}} → (c → α) → (Not c → α) → α
dite#n {u} {α} c {{h}} t e = Decidable:casesOn#n {u} {c} {λ (_ : Decidable c) → α} h e t

--def
DecidableEq#n : {u : Level} → Set u → Set (lone ⊔ u)
DecidableEq#n {u} α = (a : α) → (b : α) → Decidable (Eq#n {u} {α} a b)

--inductive 0 0->0 0 0
data Bool : Set₁ where
  Bool:false : Bool
  Bool:true : Bool

--def
#78 : Bool → Bool → Prop
#78 = Eq#n {lone} {Bool}

--def
#79 : #7 → Set₁
#79 _ = #7 → Bool

--def
#80 : Nat → Set₁
#80 = Nat:below#n {lone} {#79}

--def
#81 : Set₁
#81 = #80 Nat:zero

--def
#82#n : {u-1 : Level} → Type u-1
#82#n {u-1} = #7 → #7 → Set u-1

--def
Nat:beq:match-1#n :
  {u-1 : Level} →
    (motive : #82#n {u-1}) →
      (x$ : #7) →
        (x$1 : #7) →
          (Unit → motive Nat:zero Nat:zero) →
            ((n$ : Nat) → motive Nat:zero (Nat:succ n$)) →
              ((n$ : Nat) → motive (Nat:succ n$) Nat:zero) → ((n : Nat) → (m : Nat) → motive (Nat:succ n) (Nat:succ m)) → motive x$ x$1
Nat:beq:match-1#n {u-1} motive x$ x$1 h-1 h-2 h-3 h-4
  = Nat:casesOn#n {u-1}
    {λ (x : #7) → motive x x$1}
    x$
    (Nat:casesOn#n {u-1} {λ (x : #7) → motive Nat:zero x} x$1 (h-1 Unit:unit) (λ (n$ : Nat) → h-2 n$))
    (λ (n$ : Nat) → Nat:casesOn#n {u-1} {λ (x : #7) → motive (Nat:succ n$) x} x$1 (h-3 n$) (λ (n$1 : Nat) → h-4 n$ n$1))

--def
Nat:beq : #7 → #7 → Bool
Nat:beq x$ x$1
  = Nat:brecOn#n {lone}
    {#79}
    x$
    (λ (x$2 : #7) →
      λ (f : #80 x$2) →
        λ (x$3 : #7) →
          Nat:beq:match-1#n {lone}
            (λ (x$4 : #7) → λ (_ : #7) → #80 x$4 → Bool)
            x$2
            x$3
            (λ (_ : Unit) → λ (_ : #81) → Bool:true)
            (λ (_ : Nat) → λ (_ : #81) → Bool:false)
            (λ (n$ : Nat) → λ (_ : #80 (Nat:succ n$)) → Bool:false)
            (λ (n : Nat) → λ (m : Nat) → λ (x$4 : #80 (Nat:succ n)) → PProd#nn.fst {lone} {lone} x$4 m)
            f)
    x$1

--def
#83 : Nat → Prop
#83 x$ = (x$1 : Nat) → #78 (Nat:beq x$ x$1) Bool:true → #0 x$ x$1

--def
#84 : Nat → Set₁
#84 = Nat:below#z {#83}

--def
#85 : #7 → Bool
#85 = Nat:beq Nat:zero

--def
#86 : Set₁
#86 = #84 Nat:zero

--def
#87#z : Set₁
#87#z = Bool → Prop

--recursor 0->0 0->0 1 2
Bool:rec#z : {motive : #87#z} → motive Bool:false → motive Bool:true → (t : Bool) → motive t
Bool:rec#z {motive} false _ (Bool:false) = false
Bool:rec#z {motive} _ true (Bool:true) = true

--def
Bool:casesOn#z : {motive : #87#z} → (t : Bool) → motive Bool:false → motive Bool:true → motive t
Bool:casesOn#z {motive} t false true = Bool:rec#z {motive} false true t

--def
#87#n : {u : Level} → Type u
#87#n {u} = Bool → Set u

--recursor 0->0 0->0 1 2
Bool:rec#n : {u : Level} → {motive : #87#n {u}} → motive Bool:false → motive Bool:true → (t : Bool) → motive t
Bool:rec#n {u} {motive} false _ (Bool:false) = false
Bool:rec#n {u} {motive} _ true (Bool:true) = true

--def
Bool:casesOn#n : {u : Level} → {motive : #87#n {u}} → (t : Bool) → motive Bool:false → motive Bool:true → motive t
Bool:casesOn#n {u} {motive} t false true = Bool:rec#n {u} {motive} false true t

--def
#88#z : Bool → Prop → Prop → Prop
#88#z = Bool:casesOn#n {lone} {λ (_ : Bool) → Prop}

--def
Bool:noConfusionType#z : Prop → Bool → Bool → Prop
Bool:noConfusionType#z P v1 v2 = #88#z v1 (#88#z v2 (P → P) P) (#88#z v2 P (P → P))

--def
Bool:noConfusion#z : {P : Prop} → {v1 : Bool} → {v2 : Bool} → #78 v1 v2 → Bool:noConfusionType#z P v1 v2
Bool:noConfusion#z {P} {v1} {v2} h12
  = Eq:ndrec#zn {lone}
    {Bool}
    {v1}
    {λ (a : Bool) → #78 v1 a → Bool:noConfusionType#z P v1 a}
    (λ (_ : #78 v1 v1) → Bool:casesOn#z {λ (v1# : Bool) → Bool:noConfusionType#z P v1# v1#} v1 (λ (a : P) → a) (λ (a : P) → a))
    {v2}
    h12
    h12

--def
#89 : Set₁
#89 = (x$ : Nat) → (x$1 : Nat) → #78 (Nat:beq x$ x$1) Bool:true → Prop

--def
#90 : Prop
#90 = #78 (#85 Nat:zero) Bool:true

--def
Nat:eq-of-beq-eq-true:match-1 :
  (motive : #89) →
    (x$ : Nat) →
      (x$1 : Nat) →
        (x$2 : #78 (Nat:beq x$ x$1) Bool:true) →
          ((x$3 : #90) → motive Nat:zero Nat:zero x$3) →
            ((n$ : Nat) → (h : #78 (#85 (Nat:succ n$)) Bool:true) → motive Nat:zero (Nat:succ n$) h) →
              ((n$ : Nat) → (h : #78 (Nat:beq (Nat:succ n$) Nat:zero) Bool:true) → motive (Nat:succ n$) Nat:zero h) →
                ((n : Nat) → (m : Nat) → (h : #78 (Nat:beq (Nat:succ n) (Nat:succ m)) Bool:true) → motive (Nat:succ n) (Nat:succ m) h) →
                  motive x$ x$1 x$2
Nat:eq-of-beq-eq-true:match-1 motive x$ x$1 x$2 h-1 h-2 h-3 h-4
  = Nat:casesOn#z
    {λ (x : Nat) → (x$3 : #78 (Nat:beq x x$1) Bool:true) → motive x x$1 x$3}
    x$
    (λ (x$3 : #78 (#85 x$1) Bool:true) →
      Nat:casesOn#z
        {λ (x : Nat) → (x$4 : #78 (#85 x) Bool:true) → motive Nat:zero x x$4}
        x$1
        (λ (x$4 : #90) → h-1 x$4)
        (λ (n$ : Nat) → λ (x$4 : #78 (#85 (Nat:succ n$)) Bool:true) → h-2 n$ x$4)
        x$3)
    (λ (n$ : Nat) →
      λ (x$3 : #78 (Nat:beq (Nat:succ n$) x$1) Bool:true) →
        Nat:casesOn#z
          {λ (x : Nat) → (x$4 : #78 (Nat:beq (Nat:succ n$) x) Bool:true) → motive (Nat:succ n$) x x$4}
          x$1
          (λ (x$4 : #78 (Nat:beq (Nat:succ n$) Nat:zero) Bool:true) → h-3 n$ x$4)
          (λ (n$1 : Nat) → λ (x$4 : #78 (Nat:beq (Nat:succ n$) (Nat:succ n$1)) Bool:true) → h-4 n$ n$1 x$4)
          x$3)
    x$2

--theorem
Nat:eq-of-beq-eq-true : {n : Nat} → {m : Nat} → #78 (Nat:beq n m) Bool:true → #0 n m
Nat:eq-of-beq-eq-true {x$} {x$1} x$2
  = Nat:brecOn#z
    {#83}
    x$
    (λ (x$3 : Nat) →
      λ (f : #84 x$3) →
        λ (x$4 : Nat) →
          λ (x$5 : #78 (Nat:beq x$3 x$4) Bool:true) →
            Nat:eq-of-beq-eq-true:match-1
              (λ (x$6 : Nat) → λ (x$7 : Nat) → λ (_ : #78 (Nat:beq x$6 x$7) Bool:true) → #84 x$6 → #0 x$6 x$7)
              x$3
              x$4
              x$5
              (λ (_ : #78 (#85 Nat:zero) Bool:true) → λ (_ : #86) → #40 {Nat:zero})
              (λ (n$ : Nat) →
                λ (h : #78 (#85 (Nat:succ n$)) Bool:true) →
                  λ (_ : #86) → Bool:noConfusion#z {#37 (Nat:succ n$)} {#85 (Nat:succ n$)} {Bool:true} h)
              (λ (n$ : Nat) →
                λ (h : #78 (Nat:beq (Nat:succ n$) Nat:zero) Bool:true) →
                  λ (_ : #84 (Nat:succ n$)) → Bool:noConfusion#z {#0 (Nat:succ n$) Nat:zero} {Nat:beq (Nat:succ n$) Nat:zero} {Bool:true} h)
              (λ (n : Nat) →
                λ (m : Nat) →
                  λ (h : #78 (Nat:beq (Nat:succ n) (Nat:succ m)) Bool:true) →
                    λ (x$6 : #84 (Nat:succ n)) →
                      letFun#zz
                        {#78 (Nat:beq n m) Bool:true}
                        {λ (_ : #78 (Nat:beq n m) Bool:true) → #0 (Nat:succ n) (Nat:succ m)}
                        h
                        (λ (this : #78 (Nat:beq n m) Bool:true) →
                          letFun#zz
                            {#0 n m}
                            {λ (_ : #0 n m) → #0 (Nat:succ n) (Nat:succ m)}
                            (PProd#zn.fst {lone} x$6 m this)
                            (λ (this# : #0 n m) →
                              Eq:rec#zn {lone}
                                {Nat}
                                {n}
                                {λ (x$7 : Nat) → λ (_ : #0 n x$7) → #0 (Nat:succ n) (Nat:succ x$7)}
                                (#40 {Nat:succ n})
                                {m}
                                this#)))
              f)
    x$1
    x$2

--def
#91 : Nat → Prop
#91 x$ = (x$1 : Nat) → #78 (Nat:beq x$ x$1) Bool:false → #0 x$ x$1 → False

--def
#92 : Nat → Set₁
#92 = Nat:below#z {#91}

--def
#93 : Bool
#93 = #85 Nat:zero

--def
#94 : Set₁
#94 = #92 Nat:zero

--def
#95 : {v1 : Nat} → {v2 : Nat} → #0 v1 v2 → Nat:noConfusionType#z False v1 v2
#95 {v1} {v2} = Nat:noConfusion#z {False} {v1} {v2}

--def
#96 : Set₁
#96 = (x$ : Nat) → (x$1 : Nat) → #78 (Nat:beq x$ x$1) Bool:false → #0 x$ x$1 → Prop

--def
#97 : Prop
#97 = #78 #93 Bool:false

--def
Nat:ne-of-beq-eq-false:match-1 :
  (motive : #96) →
    (x$ : Nat) →
      (x$1 : Nat) →
        (x$2 : #78 (Nat:beq x$ x$1) Bool:false) →
          (x$3 : #0 x$ x$1) →
            ((h₁ : #97) → (x$4 : #61) → motive Nat:zero Nat:zero h₁ x$4) →
              ((n$ : Nat) → (x$4 : #78 (#85 (Nat:succ n$)) Bool:false) → (h₂ : #37 (Nat:succ n$)) → motive Nat:zero (Nat:succ n$) x$4 h₂) →
                ((n$ : Nat) →
                  (x$4 : #78 (Nat:beq (Nat:succ n$) Nat:zero) Bool:false) →
                    (h₂ : #0 (Nat:succ n$) Nat:zero) → motive (Nat:succ n$) Nat:zero x$4 h₂) →
                  ((n : Nat) →
                    (m : Nat) →
                      (h₁ : #78 (Nat:beq (Nat:succ n) (Nat:succ m)) Bool:false) →
                        (h₂ : #0 (Nat:succ n) (Nat:succ m)) → motive (Nat:succ n) (Nat:succ m) h₁ h₂) →
                    motive x$ x$1 x$2 x$3
Nat:ne-of-beq-eq-false:match-1 motive x$ x$1 x$2 x$3 h-1 h-2 h-3 h-4
  = Nat:casesOn#z
    {λ (x : Nat) → (x$4 : #78 (Nat:beq x x$1) Bool:false) → (x$5 : #0 x x$1) → motive x x$1 x$4 x$5}
    x$
    (λ (x$4 : #78 (#85 x$1) Bool:false) →
      λ (x$5 : #37 x$1) →
        Nat:casesOn#z
          {λ (x : Nat) → (x$6 : #78 (#85 x) Bool:false) → (x$7 : #37 x) → motive Nat:zero x x$6 x$7}
          x$1
          (λ (x$6 : #97) → λ (x$7 : #61) → h-1 x$6 x$7)
          (λ (n$ : Nat) → λ (x$6 : #78 (#85 (Nat:succ n$)) Bool:false) → λ (x$7 : #37 (Nat:succ n$)) → h-2 n$ x$6 x$7)
          x$4
          x$5)
    (λ (n$ : Nat) →
      λ (x$4 : #78 (Nat:beq (Nat:succ n$) x$1) Bool:false) →
        λ (x$5 : #0 (Nat:succ n$) x$1) →
          Nat:casesOn#z
            {λ (x : Nat) → (x$6 : #78 (Nat:beq (Nat:succ n$) x) Bool:false) → (x$7 : #0 (Nat:succ n$) x) → motive (Nat:succ n$) x x$6 x$7}
            x$1
            (λ (x$6 : #78 (Nat:beq (Nat:succ n$) Nat:zero) Bool:false) → λ (x$7 : #0 (Nat:succ n$) Nat:zero) → h-3 n$ x$6 x$7)
            (λ (n$1 : Nat) →
              λ (x$6 : #78 (Nat:beq (Nat:succ n$) (Nat:succ n$1)) Bool:false) → λ (x$7 : #0 (Nat:succ n$) (Nat:succ n$1)) → h-4 n$ n$1 x$6 x$7)
            x$4
            x$5)
    x$2
    x$3

--theorem
Nat:ne-of-beq-eq-false : {n : Nat} → {m : Nat} → #78 (Nat:beq n m) Bool:false → Not (#0 n m)
Nat:ne-of-beq-eq-false {x$} {x$1} x$2 x$3
  = Nat:brecOn#z
    {#91}
    x$
    (λ (x$4 : Nat) →
      λ (f : #92 x$4) →
        λ (x$5 : Nat) →
          λ (x$6 : #78 (Nat:beq x$4 x$5) Bool:false) →
            λ (x$7 : #0 x$4 x$5) →
              Nat:ne-of-beq-eq-false:match-1
                (λ (x$8 : Nat) → λ (x$9 : Nat) → λ (_ : #78 (Nat:beq x$8 x$9) Bool:false) → λ (_ : #0 x$8 x$9) → #92 x$8 → False)
                x$4
                x$5
                x$6
                x$7
                (λ (h₁ : #78 #93 Bool:false) → λ (_ : #61) → λ (_ : #94) → Bool:noConfusion#z {False} {#93} {Bool:false} h₁)
                (λ (n$ : Nat) →
                  λ (_ : #78 (#85 (Nat:succ n$)) Bool:false) → λ (h₂ : #37 (Nat:succ n$)) → λ (_ : #94) → #95 {Nat:zero} {Nat:succ n$} h₂)
                (λ (n$ : Nat) →
                  λ (_ : #78 (Nat:beq (Nat:succ n$) Nat:zero) Bool:false) →
                    λ (h₂ : #0 (Nat:succ n$) Nat:zero) → λ (_ : #92 (Nat:succ n$)) → #95 {Nat:succ n$} {Nat:zero} h₂)
                (λ (n : Nat) →
                  λ (m : Nat) →
                    λ (h₁ : #78 (Nat:beq (Nat:succ n) (Nat:succ m)) Bool:false) →
                      λ (h₂ : #0 (Nat:succ n) (Nat:succ m)) →
                        λ (x$8 : #92 (Nat:succ n)) →
                          letFun#zz
                            {#78 (Nat:beq n m) Bool:false}
                            {λ (_ : #78 (Nat:beq n m) Bool:false) → False}
                            h₁
                            (λ (this : #78 (Nat:beq n m) Bool:false) →
                              #95
                                {Nat:succ n}
                                {Nat:succ m}
                                h₂
                                (λ (h₂# : #0 n m) → absurd#z {#0 n m} {False} h₂# (PProd#zn.fst {lone} x$8 m this))))
                f)
    x$1
    x$2
    x$3

--def
#98#n : {u-1 : Level} → Type u-1
#98#n {u-1} = Bool → Set u-1

--def
Nat:decEq:match-1#n :
  {u-1 : Level} →
    (motive : #98#n {u-1}) → (x$ : Bool) → (#78 x$ Bool:true → motive Bool:true) → (#78 x$ Bool:false → motive Bool:false) → motive x$
Nat:decEq:match-1#n {u-1} motive x$ h-1 h-2
  = (λ (x$1 : Bool) → Bool:casesOn#n {u-1} {λ (x : Bool) → #78 x$ x → motive x} x$1 h-2 h-1) x$ (Eq:refl#n {lone} {Bool} x$)

--def
Nat:decEq : (n : #7) → (m : #7) → Decidable (#25 n m)
Nat:decEq n m
  = Nat:decEq:match-1#n {lone}
    (λ (_ : Bool) → Decidable (#25 n m))
    (Nat:beq n m)
    (λ (h : #78 (Nat:beq n m) Bool:true) → Decidable:isTrue {#25 n m} (Nat:eq-of-beq-eq-true {n} {m} h))
    (λ (h : #78 (Nat:beq n m) Bool:false) → Decidable:isFalse {#25 n m} (Nat:ne-of-beq-eq-false {n} {m} h))

--def
instDecidableEqNat : DecidableEq#n {lone} Nat
instDecidableEqNat = Nat:decEq

--record 3 3->3 0 6
record HMod {u : Level} {v : Level} {w : Level} (α : Type u) (β : Type v) (γ : #45 {w}) : Type (u ⊔ v ⊔ w) where
  constructor HMod:mk
  field
    hMod : α → β → γ

--record 1 1->1 0 2
record Mod {u : Level} (α : Type u) : Type u where
  constructor Mod:mk
  field
    mod : α → α → α

--def
Mod:mod : {u : Level} → {α : Type u} → {{Mod {u} α}} → α → α → α
Mod:mod {u} {α} {{self}} = Mod.mod {u} self

--def
instHMod : {u-1 : Level} → {α : Type u-1} → {{Mod {u-1} α}} → HMod {u-1} {u-1} {u-1} α α α
instHMod {u-1} {α} {{inst$}} = HMod:mk {u-1} {u-1} {u-1} {α} {α} {α} (λ (a : α) → λ (b : α) → Mod:mod {u-1} {α} {{inst$}} a b)

--def
HMod:hMod :
  {u : Level} → {v : Level} → {w : Level} → {α : Type u} → {β : Type v} → {γ : #45 {w}} → {{HMod {u} {v} {w} α β γ}} → α → β → γ
HMod:hMod {u} {v} {w} {α} {β} {γ} {{self}} = HMod.hMod {u} {v} {w} self

--def
ite#n : {u : Level} → {α : Set u} → (c : Prop) → {{Decidable c}} → α → α → α
ite#n {u} {α} c {{h}} t e = Decidable:casesOn#n {u} {c} {λ (_ : Decidable c) → α} h (λ (_ : Not c) → e) (λ (_ : c) → t)

--def
#99 : #7 → #7 → Prop
#99 = LE:le {lzero} {#7} {{instLENat}}

--def
#100 : Set₁
#100 = Bool → Prop

--def
#101 : #100
#101 = #78 Bool:false

--def
#102 : {a : Bool} → #78 a a
#102 {a} = rfl#n {lone} {Bool} {a}

--def
#103 : Prop
#103 = #101 Bool:true

--def
#104 : {v1 : Bool} → {v2 : Bool} → #78 v1 v2 → Bool:noConfusionType#z False v1 v2
#104 {v1} {v2} = Bool:noConfusion#z {False} {v1} {v2}

--def
#105 : #100
#105 = #78 Bool:true

--def
#106 : Prop
#106 = #105 Bool:false

--def
#107#n : {u-1 : Level} → Type u-1
#107#n {u-1} = Bool → Bool → Set u-1

--def
Bool:decEq:match-1#n :
  {u-1 : Level} →
    (motive : #107#n {u-1}) →
      (a$ : Bool) →
        (b$ : Bool) →
          (Unit → motive Bool:false Bool:false) →
            (Unit → motive Bool:false Bool:true) → (Unit → motive Bool:true Bool:false) → (Unit → motive Bool:true Bool:true) → motive a$ b$
Bool:decEq:match-1#n {u-1} motive a$ b$ h-1 h-2 h-3 h-4
  = Bool:casesOn#n {u-1}
    {λ (x : Bool) → motive x b$}
    a$
    (Bool:casesOn#n {u-1} {λ (x : Bool) → motive Bool:false x} b$ (h-1 Unit:unit) (h-2 Unit:unit))
    (Bool:casesOn#n {u-1} {λ (x : Bool) → motive Bool:true x} b$ (h-3 Unit:unit) (h-4 Unit:unit))

--def
Bool:decEq : (a : Bool) → (b : Bool) → Decidable (#78 a b)
Bool:decEq a b
  = Bool:decEq:match-1#n {lone}
    (λ (a$ : Bool) → λ (b$ : Bool) → Decidable (#78 a$ b$))
    a
    b
    (λ (_ : Unit) → Decidable:isTrue {#101 Bool:false} (#102 {Bool:false}))
    (λ (_ : Unit) → Decidable:isFalse {#103} (λ (h : #103) → #104 {Bool:false} {Bool:true} h))
    (λ (_ : Unit) → Decidable:isFalse {#106} (λ (h : #106) → #104 {Bool:true} {Bool:false} h))
    (λ (_ : Unit) → Decidable:isTrue {#105 Bool:true} (#102 {Bool:true}))

--def
instDecidableEqBool : DecidableEq#n {lone} Bool
instDecidableEqBool = Bool:decEq

--def
#108 : #7 → Set₁
#108 _ = #7 → Bool

--def
#109 : Nat → Set₁
#109 = Nat:below#n {lone} {#108}

--def
#110 : Set₁
#110 = #109 Nat:zero

--def
#111 : #110 → Bool
#111 _ = Bool:true

--def
Nat:ble : #7 → #7 → Bool
Nat:ble x$ x$1
  = Nat:brecOn#n {lone}
    {#108}
    x$
    (λ (x$2 : #7) →
      λ (f : #109 x$2) →
        λ (x$3 : #7) →
          Nat:beq:match-1#n {lone}
            (λ (x$4 : #7) → λ (_ : #7) → #109 x$4 → Bool)
            x$2
            x$3
            (λ (_ : Unit) → #111)
            (λ (_ : Nat) → #111)
            (λ (n$ : Nat) → λ (_ : #109 (Nat:succ n$)) → Bool:false)
            (λ (n : Nat) → λ (m : Nat) → λ (x$4 : #109 (Nat:succ n)) → PProd#nn.fst {lone} {lone} x$4 m)
            f)
    x$1

--def
#112 : #7 → Prop
#112 n = {m : #7} → #78 (Nat:ble n m) Bool:true → #99 n m

--def
#113 : Nat → Set₁
#113 = Nat:below#z {#112}

--def
#114 : Set₁
#114 = (n$ : #7) → (m$ : #7) → #78 (Nat:ble n$ m$) Bool:true → Prop

--def
#115 : #7 → Bool
#115 = Nat:ble (OfNat:ofNat {lzero} {#7} 0 {{#3}})

--def
#116 : (a : Bool) → #78 a a
#116 = Eq:refl#n {lone} {Bool}

--def
Eq:casesOn#zn :
  {u-1 : Level} →
    {α : Set u-1} →
      {a$ : α} →
        {motive : (a$1 : α) → Eq#n {u-1} {α} a$ a$1 → Prop} →
          {a$1 : α} → (t : Eq#n {u-1} {α} a$ a$1) → motive a$ (Eq:refl#n {u-1} {α} a$) → motive a$1 t
Eq:casesOn#zn {u-1} {α} {a$} {motive} {a$1} t refl = Eq:rec#zn {u-1} {α} {a$} {motive} refl {a$1} t

--def
Nat:le-of-ble-eq-true:match-1 :
  (motive : #114) →
    (n$ : #7) →
      (m$ : #7) →
        (h : #78 (Nat:ble n$ m$) Bool:true) →
          ((x$ : #7) → (h# : #78 (#115 x$) Bool:true) → motive #4 x$ h#) →
            ((n$1 : Nat) →
              (n$2 : Nat) → (h# : #78 (Nat:ble (Nat:succ n$1) (Nat:succ n$2)) Bool:true) → motive (Nat:succ n$1) (Nat:succ n$2) h#) →
              motive n$ m$ h
Nat:le-of-ble-eq-true:match-1 motive n$ m$ h h-1 h-2
  = Nat:casesOn#z
    {λ (x : #7) → (h# : #78 (Nat:ble x m$) Bool:true) → motive x m$ h#}
    n$
    (λ (h# : #78 (Nat:ble Nat:zero m$) Bool:true) → h-1 m$ h#)
    (λ (n$1 : Nat) →
      λ (h# : #78 (Nat:ble (Nat:succ n$1) m$) Bool:true) →
        Nat:casesOn#z
          {λ (x : #7) → (h#1 : #78 (Nat:ble (Nat:succ n$1) x) Bool:true) → motive (Nat:succ n$1) x h#1}
          m$
          (λ (h#1 : #78 (Nat:ble (Nat:succ n$1) Nat:zero) Bool:true) →
            Eq:casesOn#zn {lone}
              {Bool}
              {Nat:ble (Nat:succ n$1) Nat:zero}
              {λ (a$ : Bool) →
                λ (x : #78 (Nat:ble (Nat:succ n$1) Nat:zero) a$) →
                  #105 a$ →
                    HEq#z {#78 (Nat:ble (Nat:succ n$1) Nat:zero) Bool:true} h#1 {#78 (Nat:ble (Nat:succ n$1) Nat:zero) a$} x →
                      motive (Nat:succ n$1) Nat:zero h#1}
              {Bool:true}
              h#1
              (λ (h$ : #105 (Nat:ble (Nat:succ n$1) Nat:zero)) →
                Bool:noConfusion#z
                  {HEq#z
                    {#78 (Nat:ble (Nat:succ n$1) Nat:zero) Bool:true}
                    h#1
                    {#78 (Nat:ble (Nat:succ n$1) Nat:zero) (Nat:ble (Nat:succ n$1) Nat:zero)}
                    (#116 (Nat:ble (Nat:succ n$1) Nat:zero)) →
                    motive (Nat:succ n$1) Nat:zero h#1}
                  {Bool:true}
                  {Bool:false}
                  h$)
              (#116 Bool:true)
              (HEq:refl#z {#78 (Nat:ble (Nat:succ n$1) Nat:zero) Bool:true} h#1))
          (λ (n$2 : Nat) → λ (h#1 : #78 (Nat:ble (Nat:succ n$1) (Nat:succ n$2)) Bool:true) → h-2 n$1 n$2 h#1)
          h#)
    h

--theorem
Nat:le-of-ble-eq-true : {n : #7} → {m : #7} → #78 (Nat:ble n m) Bool:true → #99 n m
Nat:le-of-ble-eq-true {n} {m} h
  = Nat:brecOn#z
    {#112}
    n
    (λ (n# : #7) →
      λ (f : #113 n#) →
        λ {m# : #7} →
          λ (h# : #78 (Nat:ble n# m#) Bool:true) →
            Nat:le-of-ble-eq-true:match-1
              (λ (n$ : #7) → λ (m$ : #7) → λ (_ : #78 (Nat:ble n$ m$) Bool:true) → #113 n$ → #99 n$ m$)
              n#
              m#
              h#
              (λ (x$ : #7) → λ (_ : #78 (Nat:ble (OfNat:ofNat {lzero} {#7} 0 {{#3}}) x$) Bool:true) → λ (_ : #113 #4) → Nat:zero-le x$)
              (λ (n$ : Nat) →
                λ (n$1 : Nat) →
                  λ (h#1 : #78 (Nat:ble (Nat:succ n$) (Nat:succ n$1)) Bool:true) →
                    λ (x$ : #113 (Nat:succ n$)) → Nat:succ-le-succ {n$} {n$1} (PProd#zn.fst {lone} x$ {n$1} h#1))
              f)
    {m}
    h

--def
#117 : Nat → Prop
#117 x$ = #78 (Nat:ble x$ x$) Bool:true

--def
#118 : Nat → Set₁
#118 = Nat:below#z {#117}

--theorem
Nat:ble-self-eq-true : (n : Nat) → #78 (Nat:ble n n) Bool:true
Nat:ble-self-eq-true x$
  = Nat:brecOn#z
    {#117}
    x$
    (λ (x$1 : Nat) →
      λ (f : #118 x$1) →
        Nat:not-succ-le-zero:match-3
          (λ (x$2 : Nat) → #118 x$2 → #78 (Nat:ble x$2 x$2) Bool:true)
          x$1
          (λ (_ : Unit) → λ (_ : #118 #4) → #102 {Nat:ble #4 #4})
          (λ (n$ : Nat) → λ (x$2 : #118 (Nat:succ n$)) → PProd#zn.fst {lone} x$2)
          f)

--def
#119 : Nat → Prop
#119 x$ = (x$1 : Nat) → #78 (Nat:ble x$ x$1) Bool:true → #78 (Nat:ble x$ (Nat:succ x$1)) Bool:true

--def
#120 : Nat → Set₁
#120 = Nat:below#z {#119}

--def
#121 : #7 → Bool
#121 = Nat:ble #4

--def
#122 : Set₁
#122 = (x$ : Nat) → (x$1 : Nat) → #78 (Nat:ble x$ x$1) Bool:true → Prop

--def
Nat:ble-succ-eq-true:match-1 :
  (motive : #122) →
    (x$ : Nat) →
      (x$1 : Nat) →
        (x$2 : #78 (Nat:ble x$ x$1) Bool:true) →
          ((x$3 : Nat) → (x$4 : #78 (#121 x$3) Bool:true) → motive #4 x$3 x$4) →
            ((n : Nat) → (n$ : Nat) → (h : #78 (Nat:ble (Nat:succ n) (Nat:succ n$)) Bool:true) → motive (Nat:succ n) (Nat:succ n$) h) →
              motive x$ x$1 x$2
Nat:ble-succ-eq-true:match-1 motive x$ x$1 x$2 h-1 h-2
  = Nat:casesOn#z
    {λ (x : Nat) → (x$3 : #78 (Nat:ble x x$1) Bool:true) → motive x x$1 x$3}
    x$
    (λ (x$3 : #78 (Nat:ble Nat:zero x$1) Bool:true) → h-1 x$1 x$3)
    (λ (n$ : Nat) →
      λ (x$3 : #78 (Nat:ble (Nat:succ n$) x$1) Bool:true) →
        Nat:casesOn#z
          {λ (x : Nat) → (x$4 : #78 (Nat:ble (Nat:succ n$) x) Bool:true) → motive (Nat:succ n$) x x$4}
          x$1
          (λ (x$4 : #78 (Nat:ble (Nat:succ n$) Nat:zero) Bool:true) →
            Eq:casesOn#zn {lone}
              {Bool}
              {Nat:ble (Nat:succ n$) Nat:zero}
              {λ (a$ : Bool) →
                λ (x : #78 (Nat:ble (Nat:succ n$) Nat:zero) a$) →
                  #105 a$ →
                    HEq#z {#78 (Nat:ble (Nat:succ n$) Nat:zero) Bool:true} x$4 {#78 (Nat:ble (Nat:succ n$) Nat:zero) a$} x →
                      motive (Nat:succ n$) Nat:zero x$4}
              {Bool:true}
              x$4
              (λ (h$ : #105 (Nat:ble (Nat:succ n$) Nat:zero)) →
                Bool:noConfusion#z
                  {HEq#z
                    {#78 (Nat:ble (Nat:succ n$) Nat:zero) Bool:true}
                    x$4
                    {#78 (Nat:ble (Nat:succ n$) Nat:zero) (Nat:ble (Nat:succ n$) Nat:zero)}
                    (#116 (Nat:ble (Nat:succ n$) Nat:zero)) →
                    motive (Nat:succ n$) Nat:zero x$4}
                  {Bool:true}
                  {Bool:false}
                  h$)
              (#116 Bool:true)
              (HEq:refl#z {#78 (Nat:ble (Nat:succ n$) Nat:zero) Bool:true} x$4))
          (λ (n$1 : Nat) → λ (x$4 : #78 (Nat:ble (Nat:succ n$) (Nat:succ n$1)) Bool:true) → h-2 n$ n$1 x$4)
          x$3)
    x$2

--theorem
Nat:ble-succ-eq-true : {n : Nat} → {m : Nat} → #78 (Nat:ble n m) Bool:true → #78 (Nat:ble n (Nat:succ m)) Bool:true
Nat:ble-succ-eq-true {x$} {x$1} x$2
  = Nat:brecOn#z
    {#119}
    x$
    (λ (x$3 : Nat) →
      λ (f : #120 x$3) →
        λ (x$4 : Nat) →
          λ (x$5 : #78 (Nat:ble x$3 x$4) Bool:true) →
            Nat:ble-succ-eq-true:match-1
              (λ (x$6 : Nat) →
                λ (x$7 : Nat) → λ (_ : #78 (Nat:ble x$6 x$7) Bool:true) → #120 x$6 → #78 (Nat:ble x$6 (Nat:succ x$7)) Bool:true)
              x$3
              x$4
              x$5
              (λ (x$6 : Nat) → λ (_ : #78 (#121 x$6) Bool:true) → λ (_ : #120 #4) → #102 {#121 (Nat:succ x$6)})
              (λ (n : Nat) →
                λ (n$ : Nat) →
                  λ (h : #78 (Nat:ble (Nat:succ n) (Nat:succ n$)) Bool:true) → λ (x$6 : #120 (Nat:succ n)) → PProd#zn.fst {lone} x$6 n$ h)
              f)
    x$1
    x$2

--def
#123 : {a : #7} → {motive : #7 → Prop} → motive a → {b : #7} → #25 a b → motive b
#123 {a} {motive} = Eq:ndrec#zn {lone} {#7} {a} {motive}

--def
#124 : {a : #7} → {b : #7} → #25 a b → #25 b a
#124 {a} {b} = Eq:symm#n {lone} {#7} {a} {b}

--def
Nat:ble-eq-true-of-le:match-1 :
  {n : #7} →
    (motive : (m$ : #7) → #99 n m$ → Prop) →
      (m$ : #7) →
        (h$ : #99 n m$) →
          (Unit → motive n (Nat:le:refl {n})) →
            ((m$1 : Nat) → (h : Nat:le n m$1) → motive (Nat:succ m$1) (Nat:le:step {n} {m$1} h)) → motive m$ h$
Nat:ble-eq-true-of-le:match-1 {n} motive m$ h$ h-1 h-2
  = (λ (h$1 : Nat:le n m$) →
    Nat:le:casesOn
      {n}
      {λ (a$ : Nat) → λ (x : Nat:le n a$) → #25 m$ a$ → HEq#z {#99 n m$} h$ {Nat:le n a$} x → motive m$ h$}
      {m$}
      h$1
      (λ (h$2 : #25 m$ n) →
        #123
          {n}
          {λ (m$1 : #7) → (h$3 : #99 n m$1) → HEq#z {#99 n m$1} h$3 {Nat:le n n} (Nat:le:refl {n}) → motive m$1 h$3}
          (λ (h$3 : #99 n n) →
            λ (h$4 : HEq#z {#99 n n} h$3 {Nat:le n n} (Nat:le:refl {n})) →
              Eq:ndrec#zz
                {#99 n n}
                {Nat:le:refl {n}}
                {λ (h$5 : #99 n n) → motive n h$5}
                (h-1 Unit:unit)
                {h$3}
                (Eq:symm#z {#99 n n} {h$3} {Nat:le:refl {n}} (eq-of-heq#z {#99 n n} {h$3} {Nat:le:refl {n}} h$4)))
          {m$}
          (#124 {m$} {n} h$2)
          h$)
      (λ {m$1 : Nat} →
        λ (a$ : Nat:le n m$1) →
          λ (h$2 : #25 m$ (Nat:succ m$1)) →
            #123
              {Nat:succ m$1}
              {λ (m$2 : #7) →
                (h$3 : #99 n m$2) → HEq#z {#99 n m$2} h$3 {Nat:le n (Nat:succ m$1)} (Nat:le:step {n} {m$1} a$) → motive m$2 h$3}
              (λ (h$3 : #99 n (Nat:succ m$1)) →
                λ (h$4 : HEq#z {#99 n (Nat:succ m$1)} h$3 {Nat:le n (Nat:succ m$1)} (Nat:le:step {n} {m$1} a$)) →
                  Eq:ndrec#zz
                    {#99 n (Nat:succ m$1)}
                    {Nat:le:step {n} {m$1} a$}
                    {λ (h$5 : #99 n (Nat:succ m$1)) → motive (Nat:succ m$1) h$5}
                    (h-2 m$1 a$)
                    {h$3}
                    (Eq:symm#z
                      {#99 n (Nat:succ m$1)}
                      {h$3}
                      {Nat:le:step {n} {m$1} a$}
                      (eq-of-heq#z {#99 n (Nat:succ m$1)} {h$3} {Nat:le:step {n} {m$1} a$} h$4)))
              {m$}
              (#124 {m$} {Nat:succ m$1} h$2)
              h$))
    h$
    (Eq:refl#n {lone} {#7} m$)
    (HEq:refl#z {#99 n m$} h$)

--theorem
Nat:ble-eq-true-of-le : {n : #7} → {m : #7} → #99 n m → #78 (Nat:ble n m) Bool:true
Nat:ble-eq-true-of-le {n} {m} h
  = Nat:brecOn#z
    {λ (m# : #7) → #99 n m# → #78 (Nat:ble n m#) Bool:true}
    m
    (λ (m# : #7) →
      λ (f : Nat:below#z {λ (m#1 : #7) → #99 n m#1 → #78 (Nat:ble n m#1) Bool:true} m#) →
        λ (h# : #99 n m#) →
          Nat:ble-eq-true-of-le:match-1
            {n}
            (λ (m$ : #7) →
              λ (_ : #99 n m$) → Nat:below#z {λ (m#1 : #7) → #99 n m#1 → #78 (Nat:ble n m#1) Bool:true} m$ → #78 (Nat:ble n m$) Bool:true)
            m#
            h#
            (λ (_ : Unit) → λ (_ : Nat:below#z {λ (m#1 : #7) → #99 n m#1 → #78 (Nat:ble n m#1) Bool:true} n) → Nat:ble-self-eq-true n)
            (λ (m$ : Nat) →
              λ (h#1 : Nat:le n m$) →
                λ (x$ : Nat:below#z {λ (m#1 : #7) → #99 n m#1 → #78 (Nat:ble n m#1) Bool:true} (Nat:succ m$)) →
                  Nat:ble-succ-eq-true {n} {m$} (PProd#zn.fst {lone} x$ h#1))
            f)
    h

--theorem
Nat:not-le-of-not-ble-eq-true : {n : #7} → {m : #7} → Not (#78 (Nat:ble n m) Bool:true) → Not (#99 n m)
Nat:not-le-of-not-ble-eq-true {n} {m} h h' = absurd#z {#78 (Nat:ble n m) Bool:true} {False} (Nat:ble-eq-true-of-le {n} {m} h') h

--def
Nat:decLe : (n : #7) → (m : #7) → Decidable (#99 n m)
Nat:decLe n m
  = dite#n {lone}
    {Decidable (#99 n m)}
    (#78 (Nat:ble n m) Bool:true)
    {{instDecidableEqBool (Nat:ble n m) Bool:true}}
    (λ (h : #78 (Nat:ble n m) Bool:true) → Decidable:isTrue {#99 n m} (Nat:le-of-ble-eq-true {n} {m} h))
    (λ (h : Not (#78 (Nat:ble n m) Bool:true)) → Decidable:isFalse {#99 n m} (Nat:not-le-of-not-ble-eq-true {n} {m} h))

--def
#125 : #7 → Set₁
#125 _ = #7

--def
#126 : Set₁
#126 = PSigma#nn {lone} {lone} {#7} #125

--def
#127 : #7 → #7 → #126
#127 = PSigma:mk#nn {lone} {lone} {#7} {#125}

--def
#128 : {motive : #126 → Set₁} → (t : #126) → ((fst : #7) → (snd : #7) → motive (#127 fst snd)) → motive t
#128 {motive} = PSigma:casesOn#nnn {lone} {lone} {lone} {#7} {#125} {motive}

--def
#129 : #126 → #126 → Prop
#129
  = WellFoundedRelation#n.rel {lone}
    (invImage#nn {lone} {lone}
      {#126}
      {#7}
      (λ (x$ : #126) → #128 {λ (_ : #126) → #7} x$ (λ (x : #7) → λ (_ : #7) → x))
      (instWellFoundedRelationOfSizeOf#n {lone} {#7} {{instSizeOfNat}}))

--def
#130 : #38
#130 = #26 #4

--record 0 2->2 0 2
record And (a : Prop) (b : Prop) : Prop where
  constructor And:intro
  field
    left : a
    right : b

--def
instDecidableAnd:match-1#n :
  {u-1 : Level} →
    {q : Prop} →
      (motive : Decidable q → Set u-1) →
        (dq$ : Decidable q) →
          ((hq : q) → motive (Decidable:isTrue {q} hq)) → ((hq : Not q) → motive (Decidable:isFalse {q} hq)) → motive dq$
instDecidableAnd:match-1#n {u-1} {q} motive dq$ h-1 h-2
  = Decidable:casesOn#n {u-1} {q} {λ (x : Decidable q) → motive x} dq$ (λ (h$ : Not q) → h-2 h$) (λ (h$ : q) → h-1 h$)

--theorem
And:right : {a : Prop} → {b : Prop} → And a b → b
And:right {a} {b} self = And.right self

--theorem
instDecidableAnd:proof-1 : {p : Prop} → {q : Prop} → Not q → And p q → False
instDecidableAnd:proof-1 {p} {q} hq h = hq (And:right {p} {q} h)

--theorem
And:left : {a : Prop} → {b : Prop} → And a b → a
And:left {a} {b} self = And.left self

--theorem
instDecidableAnd:proof-2 : {p : Prop} → {q : Prop} → Not p → And p q → False
instDecidableAnd:proof-2 {p} {q} hp h = hp (And:left {p} {q} h)

--def
instDecidableAnd : {p : Prop} → {q : Prop} → {{Decidable p}} → {{Decidable q}} → Decidable (And p q)
instDecidableAnd {p} {q} {{dp}} {{dq}}
  = instDecidableAnd:match-1#n {lone}
    {p}
    (λ (_ : Decidable p) → Decidable (And p q))
    dp
    (λ (hp : p) →
      instDecidableAnd:match-1#n {lone}
        {q}
        (λ (_ : Decidable q) → Decidable (And p q))
        dq
        (λ (hq : q) → Decidable:isTrue {And p q} (And:intro {p} {q} hp hq))
        (λ (hq : Not q) → Decidable:isFalse {And p q} (instDecidableAnd:proof-1 {p} {q} hq)))
    (λ (hp : Not p) → Decidable:isFalse {And p q} (instDecidableAnd:proof-2 {p} {q} hp))

--record 3 3->3 0 6
record HSub {u : Level} {v : Level} {w : Level} (α : Type u) (β : Type v) (γ : #45 {w}) : Type (u ⊔ v ⊔ w) where
  constructor HSub:mk
  field
    hSub : α → β → γ

--record 1 1->1 0 2
record Sub {u : Level} (α : Type u) : Type u where
  constructor Sub:mk
  field
    sub : α → α → α

--def
Sub:sub : {u : Level} → {α : Type u} → {{Sub {u} α}} → α → α → α
Sub:sub {u} {α} {{self}} = Sub.sub {u} self

--def
instHSub : {u-1 : Level} → {α : Type u-1} → {{Sub {u-1} α}} → HSub {u-1} {u-1} {u-1} α α α
instHSub {u-1} {α} {{inst$}} = HSub:mk {u-1} {u-1} {u-1} {α} {α} {α} (λ (a : α) → λ (b : α) → Sub:sub {u-1} {α} {{inst$}} a b)

--def
#131 : #7 → Set₁
#131 _ = #7 → Nat

--def
#132 : Nat → Set₁
#132 = Nat:below#n {lone} {#131}

--def
#133#n : {u-1 : Level} → Type u-1
#133#n {u-1} = #7 → #7 → Set u-1

--def
Nat:mul:match-1#n :
  {u-1 : Level} →
    (motive : #133#n {u-1}) →
      (x$ : #7) → (x$1 : #7) → ((x$2 : #7) → motive x$2 #4) → ((a : #7) → (b : Nat) → motive a (Nat:succ b)) → motive x$ x$1
Nat:mul:match-1#n {u-1} motive x$ x$1 h-1 h-2 = Nat:casesOn#n {u-1} {λ (x : #7) → motive x$ x} x$1 (h-1 x$) (λ (n$ : Nat) → h-2 x$ n$)

--def
Nat:sub : #7 → #7 → Nat
Nat:sub x$ x$1
  = Nat:brecOn#n {lone}
    {#131}
    x$1
    (λ (x$2 : #7) →
      λ (f : #132 x$2) →
        λ (x$3 : #7) →
          Nat:mul:match-1#n {lone}
            (λ (_ : #7) → λ (x$4 : #7) → #132 x$4 → Nat)
            x$3
            x$2
            (λ (x$4 : #7) → λ (_ : #132 #4) → x$4)
            (λ (a : #7) → λ (b : Nat) → λ (x$4 : #132 (Nat:succ b)) → Nat:pred (PProd#nn.fst {lone} {lone} x$4 a))
            f)
    x$

--def
instSubNat : Sub {lzero} Nat
instSubNat = Sub:mk {lzero} {Nat} Nat:sub

--def
HSub:hSub :
  {u : Level} → {v : Level} → {w : Level} → {α : Type u} → {β : Type v} → {γ : #45 {w}} → {{HSub {u} {v} {w} α β γ}} → α → β → γ
HSub:hSub {u} {v} {w} {α} {β} {γ} {{self}} = HSub.hSub {u} {v} {w} self

--def
Nat:decLt : (n : #7) → (m : #7) → Decidable (LT:lt {lzero} {#7} {{instLTNat}} n m)
Nat:decLt n m = Nat:decLe (Nat:succ n) m

--recursor 2->2 1->1 1 1
postulate
  Acc:rec#nn :
    {u-1 : Level} → {u : Level} →
      {α : Set u} →
        {r : α → α → Prop} →
          {motive : (a$ : α) → Acc#n {u} {α} r a$ → Set u-1} →
            ((x : α) →
              (h : (y : α) → r y x → Acc#n {u} {α} r y) →
                ((y : α) → (a$ : r y x) → motive y (h y a$)) → motive x (Acc:intro#n {u} {α} {r} x h)) →
              {a$ : α} → (t : Acc#n {u} {α} r a$) → motive a$ t

--def
WellFounded:fixF#nn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {r : α → α → Prop} → {C : α → Set v} → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → Acc#n {u} {α} r x → C x
WellFounded:fixF#nn {u} {v} {α} {r} {C} F x a
  = Acc:rec#nn {v} {u}
    {α}
    {r}
    {λ (x# : α) → λ (_ : Acc#n {u} {α} r x#) → C x#}
    (λ (x₁ : α) → λ (_ : (y : α) → r y x₁ → Acc#n {u} {α} r y) → λ (ih : (y : α) → r y x₁ → C y) → F x₁ ih)
    {x}
    a

--def
WellFounded:fix#nn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {C : α → Set v} → {r : α → α → Prop} → WellFounded#n {u} {α} r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x
WellFounded:fix#nn {u} {v} {α} {C} {r} hwf F x = WellFounded:fixF#nn {u} {v} {α} {r} {C} F x (WellFounded:apply#n {u} {α} {r} hwf x)

--def
#134 : WellFoundedRelation#n {lone} #126
#134
  = invImage#nn {lone} {lone}
    {#126}
    {#7}
    (λ (x$ : #126) → #128 {λ (_ : #126) → #7} x$ (λ (x : #7) → λ (_ : #7) → x))
    (instWellFoundedRelationOfSizeOf#n {lone} {#7} {{instSizeOfNat}})

--theorem
Nat:modCore:-unary:proof-1 : WellFounded#n {lone} {#126} #129
Nat:modCore:-unary:proof-1 = WellFoundedRelation#n.wf {lone} #134

--def
#135 : #7 → #7 → #7
#135 = HSub:hSub {lzero} {lzero} {lzero} {#7} {#7} {#7} {{instHSub {lzero} {#7} {{instSubNat}}}}

--def
id#z : {α : Prop} → α → α
id#z {α} a = a

--def
#136 : Nat → Nat → Nat
#136 = HSub:hSub {lzero} {lzero} {lzero} {Nat} {Nat} {Nat} {{instHSub {lzero} {Nat} {{instSubNat}}}}

--theorem
Nat:lt-of-lt-of-le : {n : Nat} → {m : Nat} → {k : Nat} → #26 n m → #31 m k → #26 n k
Nat:lt-of-lt-of-le {n} {m} {k} = Nat:le-trans {Nat:succ n} {m} {k}

--def
#137 : Prop
#137 = #130 #4

--def
#138 : Prop
#138 = Not #137

--def
#139 : {b : Prop} → #137 → #138 → b
#139 {b} = absurd#z {#137} {b}

--def
#141 : Nat → Prop
#141 x$ = Not (#31 (Nat:succ x$) x$)

--def
#142 : Nat → Set₁
#142 = Nat:below#z {#141}

--theorem
Nat:not-succ-le-self : (n : Nat) → Not (#31 (Nat:succ n) n)
Nat:not-succ-le-self x$
  = Nat:brecOn#z
    {#141}
    x$
    (λ (x$1 : Nat) →
      λ (f : #142 x$1) →
        Nat:not-succ-le-zero:match-3
          (λ (x$2 : Nat) → #142 x$2 → Not (#31 (Nat:succ x$2) x$2))
          x$1
          (λ (_ : Unit) → λ (_ : #142 #4) → Nat:not-succ-le-zero #4)
          (λ (n$ : Nat) →
            λ (x$2 : #142 (Nat:succ n$)) →
              λ (h : #31 (Nat:succ (Nat:succ n$)) (Nat:succ n$)) →
                absurd#z {#31 (#16 n$ #17) n$} {False} (Nat:le-of-succ-le-succ {#16 n$ #17} {n$} h) (PProd#zn.fst {lone} x$2))
          f)

--theorem
Nat:lt-irrefl : (n : Nat) → Not (#26 n n)
Nat:lt-irrefl n = Nat:not-succ-le-self n

--def
#140 : #138
#140 = Nat:lt-irrefl #4

--theorem
Nat:lt-succ-of-le : {n : Nat} → {m : Nat} → #31 n m → #26 n (Nat:succ m)
Nat:lt-succ-of-le {n} {m} = Nat:succ-le-succ {n} {m}

--theorem
Nat:le-refl : (n : Nat) → #31 n n
Nat:le-refl n = Nat:le:refl {n}

--def
#143 : Set₁
#143 = Nat → Prop

--def
Nat:pred-le:match-1 : (motive : #143) → (x$ : Nat) → (Unit → motive Nat:zero) → ((n$ : Nat) → motive (Nat:succ n$)) → motive x$
Nat:pred-le:match-1 motive x$ h-1 h-2 = Nat:casesOn#z {λ (x : Nat) → motive x} x$ (h-1 Unit:unit) (λ (n$ : Nat) → h-2 n$)

--theorem
Nat:pred-le : (n : Nat) → #31 (Nat:pred n) n
Nat:pred-le x$
  = Nat:pred-le:match-1
    (λ (x$1 : Nat) → #31 (Nat:pred x$1) x$1)
    x$
    (λ (_ : Unit) → Nat:le:refl {Nat:pred Nat:zero})
    (λ (n$ : Nat) → Nat:le-succ (Nat:pred (Nat:succ n$)))

--theorem
Nat:sub-le : (n : Nat) → (m : Nat) → #31 (#136 n m) n
Nat:sub-le n m
  = Nat:recAux#z
    {λ (m# : Nat) → #31 (#136 n m#) n}
    (Nat:le-refl (#136 n #4))
    (λ (m# : Nat) → λ (ih : #31 (#136 n m#) n) → Nat:le-trans {Nat:pred (#136 n m#)} {#136 n m#} {n} (Nat:pred-le (#136 n m#)) ih)
    m

--theorem
congrArg#nn :
  {u : Level} → {v : Level} →
    {α : Set u} → {β : Set v} → {a₁ : α} → {a₂ : α} → (f : α → β) → Eq#n {u} {α} a₁ a₂ → Eq#n {v} {β} (f a₁) (f a₂)
congrArg#nn {u} {v} {α} {β} {a₁} {a₂} f h
  = Eq:rec#zn {u}
    {α}
    {a₁}
    {λ (x$ : α) → λ (_ : Eq#n {u} {α} a₁ x$) → Eq#n {v} {β} (f a₁) (f x$)}
    (rfl#n {v} {β} {f a₁})
    {a₂}
    h

--theorem
Nat:succ-sub-succ-eq-sub : (n : Nat) → (m : Nat) → #0 (#136 (Nat:succ n) (Nat:succ m)) (#136 n m)
Nat:succ-sub-succ-eq-sub n m
  = Nat:recAux#z
    {λ (m# : Nat) → #0 (#136 (Nat:succ n) (Nat:succ m#)) (#136 n m#)}
    (#40 {#136 (Nat:succ n) #67})
    (λ (m# : Nat) →
      λ (ih : #0 (#136 (Nat:succ n) (Nat:succ m#)) (#136 n m#)) →
        congrArg#nn {lone} {lone} {#7} {Nat} {#136 (Nat:succ n) (Nat:succ m#)} {#136 n m#} Nat:pred ih)
    m

--def
#144 : Set₁
#144 = (x$ : Nat) → (x$1 : Nat) → #130 x$ → #130 x$1 → Prop

--def
#145 : Prop
#145 = #130 Nat:zero

--def
Nat:sub-lt:match-1 :
  (motive : #144) →
    (x$ : Nat) →
      (x$1 : Nat) →
        (x$2 : #130 x$) →
          (x$3 : #130 x$1) →
            ((x$4 : Nat) → (h1 : #137) → (x$5 : #130 x$4) → motive #4 x$4 h1 x$5) →
              ((n$ : Nat) → (x$4 : #130 (#16 n$ #17)) → (h2 : #137) → motive (Nat:succ n$) #4 x$4 h2) →
                ((n : Nat) → (m : Nat) → (x$4 : #130 (#16 n #17)) → (x$5 : #130 (#16 m #17)) → motive (Nat:succ n) (Nat:succ m) x$4 x$5) →
                  motive x$ x$1 x$2 x$3
Nat:sub-lt:match-1 motive x$ x$1 x$2 x$3 h-1 h-2 h-3
  = Nat:casesOn#z
    {λ (x : Nat) → (x$4 : #130 x) → motive x x$1 x$4 x$3}
    x$
    (λ (x$4 : #145) → h-1 x$1 x$4 x$3)
    (λ (n$ : Nat) →
      λ (x$4 : #130 (Nat:succ n$)) →
        Nat:casesOn#z
          {λ (x : Nat) → (x$5 : #130 x) → motive (Nat:succ n$) x x$4 x$5}
          x$1
          (λ (x$5 : #145) → h-2 n$ x$4 x$5)
          (λ (n$1 : Nat) → λ (x$5 : #130 (Nat:succ n$1)) → h-3 n$ n$1 x$4 x$5)
          x$3)
    x$2

--theorem
Nat:sub-lt : {n : Nat} → {m : Nat} → #130 n → #130 m → #26 (#136 n m) n
Nat:sub-lt {x$} {x$1} x$2 x$3
  = Nat:sub-lt:match-1
    (λ (x$4 : Nat) → λ (x$5 : Nat) → λ (_ : #130 x$4) → λ (_ : #130 x$5) → #26 (#136 x$4 x$5) x$4)
    x$
    x$1
    x$2
    x$3
    (λ (x$4 : Nat) → λ (h1 : #137) → λ (_ : #130 x$4) → #139 {#26 (#136 #4 x$4) #4} h1 #140)
    (λ (n$ : Nat) → λ (_ : #130 (#16 n$ #17)) → λ (h2 : #137) → #139 {#26 (#136 (#16 n$ #17) #4) (#16 n$ #17)} h2 #140)
    (λ (n : Nat) →
      λ (m : Nat) →
        λ (_ : #130 (#16 n #17)) →
          λ (_ : #130 (#16 m #17)) →
            Eq:rec#zn {lone}
              {Nat}
              {#136 n m}
              {λ (x$4 : Nat) → λ (_ : #0 (#136 n m) x$4) → #26 x$4 (#16 n #17)}
              (letFun#zz
                {#26 (#136 n m) (Nat:succ n)}
                {λ (_ : #26 (#136 n m) (Nat:succ n)) → #26 (#136 n m) (Nat:succ n)}
                (Nat:lt-succ-of-le {#136 n m} {n} (Nat:sub-le n m))
                (λ (this : #26 (#136 n m) (Nat:succ n)) → this))
              {#136 (Nat:succ n) (Nat:succ m)}
              (#15 {#136 (Nat:succ n) (Nat:succ m)} {#136 n m} (Nat:succ-sub-succ-eq-sub n m)))

--recursor 2->2 0->0 1 1
And:rec#z :
  {a : Prop} →
    {b : Prop} →
      {motive : And a b → Prop} → ((left : a) → (right : b) → motive (And:intro {a} {b} left right)) → (t : And a b) → motive t
And:rec#z {a} {b} {motive} intro (And:intro left right) = intro left right

--def
And:casesOn#z :
  {a : Prop} →
    {b : Prop} →
      {motive : And a b → Prop} → (t : And a b) → ((left : a) → (right : b) → motive (And:intro {a} {b} left right)) → motive t
And:casesOn#z {a} {b} {motive} t intro = And:rec#z {a} {b} {motive} (λ (left : a) → λ (right : b) → intro left right) t

--def
Nat:div-rec-lemma:match-1 :
  {x : Nat} →
    {y : Nat} →
      (motive : And (#130 y) (#31 y x) → Prop) →
        (x$ : And (#130 y) (#31 y x)) → ((ypos : #130 y) → (ylex : #31 y x) → motive (And:intro {#130 y} {#31 y x} ypos ylex)) → motive x$
Nat:div-rec-lemma:match-1 {x} {y} motive x$ h-1
  = And:casesOn#z
    {#130 y}
    {#31 y x}
    {λ (x# : And (#130 y) (#31 y x)) → motive x#}
    x$
    (λ (left$ : #130 y) → λ (right$ : #31 y x) → h-1 left$ right$)

--theorem
Nat:div-rec-lemma : {x : Nat} → {y : Nat} → And (#130 y) (#31 y x) → #26 (#136 x y) x
Nat:div-rec-lemma {x} {y} x$
  = Nat:div-rec-lemma:match-1
    {x}
    {y}
    (λ (_ : And (#130 y) (#31 y x)) → #26 (#136 x y) x)
    x$
    (λ (ypos : #130 y) → λ (ylex : #31 y x) → Nat:sub-lt {x} {y} (Nat:lt-of-lt-of-le {#4} {y} {x} ypos ylex) ypos)

--theorem
Nat:modCore:-unary:proof-2 : (x : #7) → (y : #7) → And (#130 y) (#99 y x) → #129 (#127 (#135 x y) y) (#127 x y)
Nat:modCore:-unary:proof-2 x y h$ = id#z {#129 (#127 (#135 x y) y) (#127 x y)} (Nat:div-rec-lemma {x} {y} h$)

--def
Nat:modCore:-unary : #126 → Nat
Nat:modCore:-unary
  = WellFounded:fix#nn {lone} {lone}
    {#126}
    {λ (_ : #126) → Nat}
    {#129}
    Nat:modCore:-unary:proof-1
    (λ (x : #126) →
      λ (a$ : (y : #126) → #129 y x → Nat) →
        #128
          {λ (-x : #126) → ((y : #126) → #129 y -x → Nat) → Nat}
          x
          (λ (x# : #7) →
            λ (y : #7) →
              λ (a$1 : (y# : #126) → #129 y# (#127 x# y) → Nat) →
                dite#n {lone}
                  {Nat}
                  (And (#130 y) (#99 y x#))
                  {{instDecidableAnd {#130 y} {#99 y x#} {{Nat:decLt #4 y}} {{Nat:decLe y x#}}}}
                  (λ (h$ : And (#130 y) (#99 y x#)) →
                    a$1
                      (#127 (HSub:hSub {lzero} {lzero} {lzero} {#7} {#7} {#7} {{instHSub {lzero} {#7} {{instSubNat}}}} x# y) y)
                      (Nat:modCore:-unary:proof-2 x# y h$))
                  (λ (_ : Not (And (#130 y) (#99 y x#))) → x#))
          a$)

--def
Nat:modCore : #7 → #7 → Nat
Nat:modCore x y = Nat:modCore:-unary (PSigma:mk#nn {lone} {lone} {#7} {λ (_ : #7) → #7} x y)

--def
#146#n : {u-1 : Level} → Type u-1
#146#n {u-1} = #7 → #7 → Set u-1

--def
namedPattern#n : {u : Level} → {α : Set u} → (x : α) → (a : α) → Eq#n {u} {α} x a → α
namedPattern#n {u} {α} x a _ = a

--def
#147 : (x : #7) → (a : #7) → #25 x a → #7
#147 = namedPattern#n {lone} {#7}

--def
Nat:mod:match-1#n :
  {u-1 : Level} →
    (motive : #146#n {u-1}) →
      (x$ : #7) →
        (x$1 : #7) →
          ((x$2 : #7) → motive #4 x$2) →
            ((n : #7) → (n$ : Nat) → (h$ : #25 n (#16 n$ #17)) → (m : #7) → motive (#147 n (Nat:succ n$) h$) m) → motive x$ x$1
Nat:mod:match-1#n {u-1} motive x$ x$1 h-1 h-2
  = Nat:casesOn#n {u-1}
    {λ (x : #7) → motive x x$1}
    x$
    (h-1 x$1)
    (λ (n$ : Nat) → h-2 (Nat:succ n$) n$ (Eq:refl#n {lone} {#7} (Nat:succ n$)) x$1)

--def
Nat:mod : #7 → #7 → Nat
Nat:mod x$ x$1
  = Nat:mod:match-1#n {lone}
    (λ (_ : #7) → λ (_ : #7) → Nat)
    x$
    x$1
    (λ (_ : #7) → #4)
    (λ (n : #7) →
      λ (n$ : Nat) →
        λ (_ : #25 n (#16 n$ #17)) →
          λ (m : #7) → ite#n {lone} {Nat} (LE:le {lzero} {#7} {{instLENat}} m n) {{Nat:decLe m n}} (Nat:modCore n m) n)

--def
Nat:instMod : Mod {lzero} Nat
Nat:instMod = Mod:mk {lzero} {Nat} Nat:mod

--def
#148 : WellFoundedRelation#n {lone} #21
#148
  = invImage#nn {lone} {lone}
    {#21}
    {#7}
    (λ (x$ : #21) → #23 {λ (_ : #21) → #7} x$ (λ (m : #7) → λ (_ : #7) → m))
    (instWellFoundedRelationOfSizeOf#n {lone} {#7} {{instSizeOfNat}})

--theorem
Nat:gcd:-unary:proof-1 : WellFounded#n {lone} {#21} #24
Nat:gcd:-unary:proof-1 = WellFoundedRelation#n.wf {lone} #148

--def
#11 : Prop → Prop → Prop
#11 = Eq#n {lone} {Prop}

--def
#149 : #7 → #7 → #7
#149 = HMod:hMod {lzero} {lzero} {lzero} {#7} {#7} {#7} {{instHMod {lzero} {#7} {{Nat:instMod}}}}

--record 0 2->2 0 2
record Iff (a : Prop) (b : Prop) : Prop where
  constructor Iff:intro
  field
    mp : a → b
    mpr : b → a

--def
GT:gt : {u : Level} → {α : Type u} → {{LT {u} α}} → α → α → Prop
GT:gt {u} {α} {{inst$}} a b = LT:lt {u} {α} {{inst$}} b a

--theorem
Iff:refl : (a : Prop) → Iff a a
Iff:refl a = Iff:intro {a} {a} (λ (h : a) → h) (λ (h : a) → h)

--theorem
Iff:rfl : {a : Prop} → Iff a a
Iff:rfl {a} = Iff:refl a

--theorem
gt-iff-lt :
  {u : Level} →
    {α : Type u} → {{inst$ : LT {u} α}} → {x : α} → {y : α} → Iff (GT:gt {u} {α} {{inst$}} x y) (LT:lt {u} {α} {{inst$}} y x)
gt-iff-lt {u} {α} {{inst$}} {x} {y} = Iff:rfl {GT:gt {u} {α} {{inst$}} x y}

--axiom
postulate propext : {a : Prop} → {b : Prop} → Iff a b → #11 a b

--theorem
Init:Core:-auxLemma:7 :
  {u : Level} →
    {α : Type u} → {{inst$ : LT {u} α}} → {x : α} → {y : α} → #11 (GT:gt {u} {α} {{inst$}} x y) (LT:lt {u} {α} {{inst$}} y x)
Init:Core:-auxLemma:7 {u} {α} {{inst$}} {x} {y}
  = propext {GT:gt {u} {α} {{inst$}} x y} {LT:lt {u} {α} {{inst$}} y x} (gt-iff-lt {u} {α} {{inst$}} {x} {y})

--def
Eq:mpr#z : {α : Prop} → {β : Prop} → #46#z α β → β → α
Eq:mpr#z {α} {β} h b
  = Eq:rec#zn {lone} {Prop} {β} {λ (x$ : Prop) → λ (_ : #46#z β x$) → x$} b {α} (Eq:symm#n {lone} {Prop} {α} {β} h)

--def
#13 : {a₁ : Nat} → {a₂ : Nat} → (f : Nat → Prop) → #0 a₁ a₂ → #11 (f a₁) (f a₂)
#13 {a₁} {a₂} = congrArg#nn {lone} {lone} {Nat} {Prop} {a₁} {a₂}

--def
#19 : Nat → Nat → Nat
#19 = HMod:hMod {lzero} {lzero} {lzero} {Nat} {Nat} {Nat} {{instHMod {lzero} {Nat} {{Nat:instMod}}}}

--def
#150 : Nat → Nat → Prop
#150 = GT:gt {lzero} {Nat} {{instLTNat}}

--def
And:symm:match-1 :
  {a : Prop} →
    {b : Prop} → (motive : And a b → Prop) → (x$ : And a b) → ((ha : a) → (hb : b) → motive (And:intro {a} {b} ha hb)) → motive x$
And:symm:match-1 {a} {b} motive x$ h-1
  = And:casesOn#z {a} {b} {λ (x : And a b) → motive x} x$ (λ (left$ : a) → λ (right$ : b) → h-1 left$ right$)

--recursor 1->1 0->0 1 2
Decidable:rec#z :
  {p : Prop} →
    {motive : Decidable p → Prop} →
      ((h : Not p) → motive (Decidable:isFalse {p} h)) → ((h : p) → motive (Decidable:isTrue {p} h)) → (t : Decidable p) → motive t
Decidable:rec#z {p} {motive} isFalse _ (Decidable:isFalse h) = isFalse h
Decidable:rec#z {p} {motive} _ isTrue (Decidable:isTrue h) = isTrue h

--def
Decidable:casesOn#z :
  {p : Prop} →
    {motive : Decidable p → Prop} →
      (t : Decidable p) → ((h : Not p) → motive (Decidable:isFalse {p} h)) → ((h : p) → motive (Decidable:isTrue {p} h)) → motive t
Decidable:casesOn#z {p} {motive} t isFalse isTrue = Decidable:rec#z {p} {motive} (λ (h : Not p) → isFalse h) (λ (h : p) → isTrue h) t

--def
Decidable:not-and-iff-or-not:match-1 :
  (p : Prop) →
    (q : Prop) →
      (motive : Decidable p → Decidable q → Prop) →
        (d₁$ : Decidable p) →
          (d₂$ : Decidable q) →
            ((h₁ : p) → (h₂ : q) → motive (Decidable:isTrue {p} h₁) (Decidable:isTrue {q} h₂)) →
              ((x$ : Decidable p) → (h₂ : Not q) → motive x$ (Decidable:isFalse {q} h₂)) →
                ((h₁ : Not p) → (x$ : Decidable q) → motive (Decidable:isFalse {p} h₁) x$) → motive d₁$ d₂$
Decidable:not-and-iff-or-not:match-1 p q motive d₁$ d₂$ h-1 h-2 h-3
  = Decidable:casesOn#z
    {p}
    {λ (x : Decidable p) → motive x d₂$}
    d₁$
    (λ (h$ : Not p) →
      Decidable:casesOn#z
        {q}
        {λ (x : Decidable q) → motive (Decidable:isFalse {p} h$) x}
        d₂$
        (λ (h$1 : Not q) → h-2 (Decidable:isFalse {p} h$) h$1)
        (λ (h$1 : q) → h-3 h$ (Decidable:isTrue {q} h$1)))
    (λ (h$ : p) →
      Decidable:casesOn#z
        {q}
        {λ (x : Decidable q) → motive (Decidable:isTrue {p} h$) x}
        d₂$
        (λ (h$1 : Not q) → h-2 (Decidable:isTrue {p} h$) h$1)
        (λ (h$1 : q) → h-1 h$ h$1))

--def
Decidable:not-and-iff-or-not:match-2 :
  (p : Prop) →
    (q : Prop) →
      (motive : Or (Not p) (Not q) → Prop) →
        (h$ : Or (Not p) (Not q)) →
          ((h : Not p) → motive (Or:inl {Not p} {Not q} h)) → ((h : Not q) → motive (Or:inr {Not p} {Not q} h)) → motive h$
Decidable:not-and-iff-or-not:match-2 p q motive h$ h-1 h-2
  = Or:casesOn {Not p} {Not q} {λ (x : Or (Not p) (Not q)) → motive x} h$ (λ (h$1 : Not p) → h-1 h$1) (λ (h$1 : Not q) → h-2 h$1)

--theorem
Decidable:not-and-iff-or-not :
  (p : Prop) → (q : Prop) → {{Decidable p}} → {{Decidable q}} → Iff (Not (And p q)) (Or (Not p) (Not q))
Decidable:not-and-iff-or-not p q {{d₁}} {{d₂}}
  = Iff:intro
    {Not (And p q)}
    {Or (Not p) (Not q)}
    (λ (h : Not (And p q)) →
      Decidable:not-and-iff-or-not:match-1
        p
        q
        (λ (_ : Decidable p) → λ (_ : Decidable q) → Or (Not p) (Not q))
        d₁
        d₂
        (λ (h₁ : p) → λ (h₂ : q) → absurd#z {And p q} {Or (Not p) (Not q)} (And:intro {p} {q} h₁ h₂) h)
        (λ (_ : Decidable p) → λ (h₂ : Not q) → Or:inr {Not p} {Not q} h₂)
        (λ (h₁ : Not p) → λ (_ : Decidable q) → Or:inl {Not p} {Not q} h₁))
    (λ (h : Or (Not p) (Not q)) →
      λ (x$ : And p q) →
        And:symm:match-1
          {p}
          {q}
          (λ (_ : And p q) → False)
          x$
          (λ (hp : p) →
            λ (hq : q) →
              Decidable:not-and-iff-or-not:match-2
                p
                q
                (λ (_ : Or (Not p) (Not q)) → False)
                h
                (λ (h# : Not p) → h# hp)
                (λ (h# : Not q) → h# hq)))

--def
Eq:mp#z : {α : Prop} → {β : Prop} → #46#z α β → α → β
Eq:mp#z {α} {β} h a = Eq:rec#zn {lone} {Prop} {α} {λ (x$ : Prop) → λ (_ : #46#z α x$) → x$} a {β} h

--theorem
Iff:mp : {a : Prop} → {b : Prop} → Iff a b → a → b
Iff:mp {a} {b} self = Iff.mp self

--def
GE:ge : {u : Level} → {α : Type u} → {{LE {u} α}} → α → α → Prop
GE:ge {u} {α} {{inst$}} a b = LE:le {u} {α} {{inst$}} b a

--def
#151 : Nat → Nat → Prop
#151 = GE:ge {lzero} {Nat} {{instLENat}}

--theorem
Nat:le-succ-of-le : {n : Nat} → {m : Nat} → #31 n m → #31 n (Nat:succ m)
Nat:le-succ-of-le {n} {m} h = Nat:le-trans {n} {m} {Nat:succ m} h (Nat:le-succ m)

--def
Nat:lt-or-ge:match-1 :
  (n : Nat) →
    (m : Nat) →
      (motive : Or (#0 m n) (#26 m n) → Prop) →
        (x$ : Or (#0 m n) (#26 m n)) →
          ((h1 : #0 m n) → motive (Or:inl {#0 m n} {#26 m n} h1)) → ((h1 : #26 m n) → motive (Or:inr {#0 m n} {#26 m n} h1)) → motive x$
Nat:lt-or-ge:match-1 n m motive x$ h-1 h-2
  = Or:casesOn
    {#0 m n}
    {#26 m n}
    {λ (x : Or (#0 m n) (#26 m n)) → motive x}
    x$
    (λ (h$ : #0 m n) → h-1 h$)
    (λ (h$ : #26 m n) → h-2 h$)

--def
Nat:lt-or-ge:match-2 :
  (n : Nat) →
    (m : Nat) →
      (motive : Or (#26 n m) (#151 n m) → Prop) →
        (x$ : Or (#26 n m) (#151 n m)) →
          ((h : #26 n m) → motive (Or:inl {#26 n m} {#151 n m} h)) → ((h : #151 n m) → motive (Or:inr {#26 n m} {#151 n m} h)) → motive x$
Nat:lt-or-ge:match-2 n m motive x$ h-1 h-2
  = Or:casesOn
    {#26 n m}
    {#151 n m}
    {λ (x : Or (#26 n m) (#151 n m)) → motive x}
    x$
    (λ (h$ : #26 n m) → h-1 h$)
    (λ (h$ : #151 n m) → h-2 h$)

--theorem
Nat:lt-or-ge : (n : Nat) → (m : Nat) → Or (#26 n m) (#151 n m)
Nat:lt-or-ge n m
  = Nat:brecOn#z
    {λ (m# : Nat) → Or (#26 n m#) (#151 n m#)}
    m
    (λ (m# : Nat) →
      λ (f : Nat:below#z {λ (m#1 : Nat) → Or (#26 n m#1) (#151 n m#1)} m#) →
        Nat:zero-le:match-1
          (λ (m$ : Nat) → Nat:below#z {λ (m#1 : Nat) → Or (#26 n m#1) (#151 n m#1)} m$ → Or (#26 n m$) (#151 n m$))
          m#
          (λ (_ : Unit) →
            λ (_ : Nat:below#z {λ (m#1 : Nat) → Or (#26 n m#1) (#151 n m#1)} Nat:zero) →
              Or:inr {#26 n Nat:zero} {#151 n Nat:zero} (Nat:zero-le n))
          (λ (n# : Nat) →
            λ (x$ : Nat:below#z {λ (m#1 : Nat) → Or (#26 n m#1) (#151 n m#1)} (Nat:succ n#)) →
              Nat:lt-or-ge:match-2
                n
                n#
                (λ (_ : Or (#26 n n#) (#151 n n#)) → Or (#26 n (Nat:succ n#)) (#151 n (Nat:succ n#)))
                (PProd#zn.fst {lone} x$)
                (λ (h : #26 n n#) → Or:inl {#26 n (Nat:succ n#)} {#151 n (Nat:succ n#)} (Nat:le-succ-of-le {Nat:succ n} {n#} h))
                (λ (h : #151 n n#) →
                  Nat:lt-or-ge:match-1
                    n
                    n#
                    (λ (_ : Or (#0 n# n) (#26 n# n)) → Or (#26 n (Nat:succ n#)) (#151 n (Nat:succ n#)))
                    (Nat:eq-or-lt-of-le {n#} {n} h)
                    (λ (h1 : #0 n# n) →
                      Or:inl
                        {#26 n (Nat:succ n#)}
                        {#151 n (Nat:succ n#)}
                        (Eq:rec#zn {lone}
                          {Nat}
                          {n#}
                          {λ (x$1 : Nat) → λ (_ : #0 n# x$1) → #26 x$1 (Nat:succ n#)}
                          (Nat:le-refl (Nat:succ n#))
                          {n}
                          h1))
                    (λ (h1 : #26 n# n) → Or:inr {#26 n (Nat:succ n#)} {#151 n (Nat:succ n#)} h1)))
          f)

--def
Or:elim:match-1 :
  {a : Prop} →
    {b : Prop} →
      (motive : Or a b → Prop) →
        (h$ : Or a b) → ((h : a) → motive (Or:inl {a} {b} h)) → ((h : b) → motive (Or:inr {a} {b} h)) → motive h$
Or:elim:match-1 {a} {b} motive h$ h-1 h-2
  = Or:casesOn {a} {b} {λ (x : Or a b) → motive x} h$ (λ (h$1 : a) → h-1 h$1) (λ (h$1 : b) → h-2 h$1)

--theorem
Or:elim : {a : Prop} → {b : Prop} → {c : Prop} → Or a b → (a → c) → (b → c) → c
Or:elim {a} {b} {c} h left right = Or:elim:match-1 {a} {b} (λ (_ : Or a b) → c) h (λ (h# : a) → left h#) (λ (h# : b) → right h#)

--theorem
Or:resolve-right : {a : Prop} → {b : Prop} → Or a b → Not b → a
Or:resolve-right {a} {b} h nb = Or:elim {a} {b} {a} h (id#z {a}) (λ (x$ : b) → absurd#z {b} {a} x$ nb)

--theorem
Nat:gt-of-not-le : {n : Nat} → {m : Nat} → Not (#31 n m) → #150 n m
Nat:gt-of-not-le {n} {m} h = Or:resolve-right {#26 m n} {GE:ge {lzero} {Nat} {{instLENat}} m n} (Nat:lt-or-ge m n) h

--def
#152 : (c : Prop) → {{Decidable c}} → Nat → Nat → Nat
#152 = ite#n {lone} {Nat}

--def
#153 : (m : #7) → Decidable (LT:lt {lzero} {#7} {{instLTNat}} #4 m)
#153 = Nat:decLt #4

--def
if-pos:match-1 :
  {c : Prop} →
    (motive : Decidable c → Prop) →
      (h$ : Decidable c) →
        ((h$1 : c) → motive (Decidable:isTrue {c} h$1)) → ((hnc : Not c) → motive (Decidable:isFalse {c} hnc)) → motive h$
if-pos:match-1 {c} motive h$ h-1 h-2
  = Decidable:casesOn#z {c} {λ (x : Decidable c) → motive x} h$ (λ (h$1 : Not c) → h-2 h$1) (λ (h$1 : c) → h-1 h$1)

--theorem
if-neg#n :
  {u : Level} →
    {c : Prop} → {h : Decidable c} → Not c → {α : Set u} → {t : α} → {e : α} → Eq#n {u} {α} (ite#n {u} {α} c {{h}} t e) e
if-neg#n {u} {c} {h} hnc {α} {t} {e}
  = if-pos:match-1
    {c}
    (λ (h$ : Decidable c) → Eq#n {u} {α} (ite#n {u} {α} c {{h$}} t e) e)
    h
    (λ (hc : c) → absurd#z {c} {Eq#n {u} {α} (ite#n {u} {α} c {{Decidable:isTrue {c} hc}} t e) e} hc hnc)
    (λ (h$ : Not c) → rfl#n {u} {α} {ite#n {u} {α} c {{Decidable:isFalse {c} h$}} t e})

--def
#154 : #7 → Nat
#154 = Nat:modCore #4

--def
#155 : #7 → Nat
#155 = Nat:mod #4

--def
#156 : Set₁
#156 = #7 → #7

--def
#157 : #156
#157 = #135 #4

--def
Decidable:byCases:match-1#z :
  {p : Prop} →
    (motive : Decidable p → Prop) →
      (dec$ : Decidable p) →
        ((h : p) → motive (Decidable:isTrue {p} h)) → ((h : Not p) → motive (Decidable:isFalse {p} h)) → motive dec$
Decidable:byCases:match-1#z {p} motive dec$ h-1 h-2
  = Decidable:casesOn#z {p} {λ (x : Decidable p) → motive x} dec$ (λ (h$ : Not p) → h-2 h$) (λ (h$ : p) → h-1 h$)

--def
iteInduction#nz :
  {u-1 : Level} →
    {α : Set u-1} →
      {c : Prop} →
        {{inst : Decidable c}} →
          {motive : α → Prop} → {t : α} → {e : α} → (c → motive t) → (Not c → motive e) → motive (ite#n {u-1} {α} c {{inst}} t e)
iteInduction#nz {u-1} {α} {c} {{inst}} {motive} {t} {e} hpos hneg
  = Decidable:byCases:match-1#z
    {c}
    (λ (inst$ : Decidable c) → motive (ite#n {u-1} {α} c {{inst$}} t e))
    inst
    (λ (h : c) → hpos h)
    (λ (h : Not c) → hneg h)

--theorem
Nat:mod:eq-2 :
  (x$ : Nat) →
    (n : Nat) →
      #0
        (Nat:mod (Nat:succ n) x$)
        (#152 (#99 x$ (Nat:succ n)) {{Nat:decLe x$ (Nat:succ n)}} (Nat:modCore (Nat:succ n) x$) (Nat:succ n))
Nat:mod:eq-2 x n = #62 (Nat:mod (Nat:succ n) x)

--theorem
Eq:trans#n : {u : Level} → {α : Set u} → {a : α} → {b : α} → {c : α} → Eq#n {u} {α} a b → Eq#n {u} {α} b c → Eq#n {u} {α} a c
Eq:trans#n {u} {α} {a} {b} {c} h₁ h₂
  = Eq:rec#zn {u} {α} {b} {λ (x$ : α) → λ (_ : Eq#n {u} {α} b x$) → Eq#n {u} {α} a x$} h₁ {c} h₂

--def
#18 : {a : Nat} → {b : Nat} → {c : Nat} → #0 a b → #0 b c → #0 a c
#18 {a} {b} {c} = Eq:trans#n {lone} {Nat} {a} {b} {c}

--def
#158 : #126 → Set₁
#158 _ = Nat

--def
#159 :
  (t : #126) → ((fst : #7) → (snd : #7) → ((y : #126) → #129 y (#127 fst snd) → Nat) → Nat) → ((y : #126) → #129 y t → Nat) → Nat
#159 = #128 {λ (-x : #126) → ((y : #126) → #129 y -x → Nat) → Nat}

--def
#160 : (x : #7) → (y : #7) → ((y# : #126) → #129 y# (#127 x y) → Nat) → Nat
#160 x y a$
  = dite#n {lone}
    {Nat}
    (And (#130 y) (#99 y x))
    {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
    (λ (h$ : And (#130 y) (#99 y x)) → a$ (#127 (#135 x y) y) (Nat:modCore:-unary:proof-2 x y h$))
    (λ (_ : Not (And (#130 y) (#99 y x))) → x)

--def
#161 : (x : #126) → ((y : #126) → #129 y x → Nat) → Nat
#161 x a$ = #159 x #160 a$

--def
#162 : #126 → Nat
#162 = WellFounded:fix#nn {lone} {lone} {#126} {#158} {#129} Nat:modCore:-unary:proof-1 #161

--theorem
postulate
  WellFounded:fixFEq#nn :
    {u : Level} → {v : Level} →
      {α : Set u} →
        {r : α → α → Prop} →
          {C : α → Set v} →
            (F : (x : α) → ((y : α) → r y x → C y) → C x) →
              (x : α) →
                (acx : Acc#n {u} {α} r x) →
                  Eq#n {v}
                    {C x}
                    (WellFounded:fixF#nn {u} {v} {α} {r} {C} F x acx)
                    (F
                      x
                      (λ (y : α) →
                        λ (p : r y x) → WellFounded:fixF#nn {u} {v} {α} {r} {C} F y (Acc:inv#n {u} {α} {r} {x} {y} acx p)))

--theorem
WellFounded:fix-eq#nn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {C : α → Set v} →
        {r : α → α → Prop} →
          (hwf : WellFounded#n {u} {α} r) →
            (F : (x : α) → ((y : α) → r y x → C y) → C x) →
              (x : α) →
                Eq#n {v}
                  {C x}
                  (WellFounded:fix#nn {u} {v} {α} {C} {r} hwf F x)
                  (F x (λ (y : α) → λ (_ : r y x) → WellFounded:fix#nn {u} {v} {α} {C} {r} hwf F y))
WellFounded:fix-eq#nn {u} {v} {α} {C} {r} hwf F x
  = WellFounded:fixFEq#nn {u} {v} {α} {r} {C} F x (WellFounded:apply#n {u} {α} {r} hwf x)

--theorem
Nat:modCore:eq-1 :
  (x : Nat) →
    (y : Nat) →
      #0
        (Nat:modCore x y)
        (#152
          (And (#130 y) (#99 y x))
          {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
          (Nat:modCore (#135 x y) y)
          x)
Nat:modCore:eq-1 x y
  = id#z
    {#0
      (Nat:modCore x y)
      (#152
        (And (#130 y) (#99 y x))
        {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
        (Nat:modCore (#135 x y) y)
        x)}
    (id#z
      {#0
        (Nat:modCore:-unary (#127 x y))
        (#152
          (And (#130 y) (#99 y x))
          {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
          (Nat:modCore (#135 x y) y)
          x)}
      (#18
        {#162 (#127 x y)}
        {#159 (#127 x y) #160 (λ (y# : #126) → λ (_ : #129 y# (#127 x y)) → #162 y#)}
        {#152
          (And (#130 y) (#99 y x))
          {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
          (Nat:modCore (#135 x y) y)
          x}
        (WellFounded:fix-eq#nn {lone} {lone} {#126} {#158} {#129} Nat:modCore:-unary:proof-1 #161 (#127 x y))
        (#62 (#159 (#127 x y) #160 (λ (y# : #126) → λ (_ : #129 y# (#127 x y)) → #162 y#)))))

--def
#163 : Set₁
#163 = Nat → Nat → Prop

--def
Nat:modCore-eq-mod:match-1 :
  (motive : #163) →
    (n$ : Nat) → (m$ : Nat) → ((x$ : Nat) → motive #4 x$) → ((n$1 : Nat) → (x$ : Nat) → motive (Nat:succ n$1) x$) → motive n$ m$
Nat:modCore-eq-mod:match-1 motive n$ m$ h-1 h-2 = Nat:casesOn#z {λ (x : Nat) → motive x m$} n$ (h-1 m$) (λ (n$1 : Nat) → h-2 n$1 m$)

--def
Nat:modCore-eq-mod:match-2 :
  (x$ : Nat) →
    (motive : And (#130 x$) (#99 x$ #4) → Prop) →
      (x$1 : And (#130 x$) (#99 x$ #4)) →
        ((hlt : #130 x$) → (hle : #99 x$ #4) → motive (And:intro {#130 x$} {#99 x$ #4} hlt hle)) → motive x$1
Nat:modCore-eq-mod:match-2 x$ motive x$1 h-1
  = And:casesOn#z
    {#130 x$}
    {#99 x$ #4}
    {λ (x : And (#130 x$) (#99 x$ #4)) → motive x}
    x$1
    (λ (left$ : #130 x$) → λ (right$ : #99 x$ #4) → h-1 left$ right$)

--def
Nat:modCore-eq-mod:match-3 :
  (n$ : Nat) →
    (x$ : Nat) →
      (motive : And (#130 x$) (#99 x$ (#16 n$ #17)) → Prop) →
        (x$1 : And (#130 x$) (#99 x$ (#16 n$ #17))) →
          ((-hlt : #130 x$) → (hle : #99 x$ (#16 n$ #17)) → motive (And:intro {#130 x$} {#99 x$ (#16 n$ #17)} -hlt hle)) → motive x$1
Nat:modCore-eq-mod:match-3 n$ x$ motive x$1 h-1
  = And:casesOn#z
    {#130 x$}
    {#99 x$ (#16 n$ #17)}
    {λ (x : And (#130 x$) (#99 x$ (#16 n$ #17))) → motive x}
    x$1
    (λ (left$ : #130 x$) → λ (right$ : #99 x$ (#16 n$ #17)) → h-1 left$ right$)

--theorem
Nat:modCore-eq-mod : (n : Nat) → (m : Nat) → #0 (Nat:modCore n m) (#19 n m)
Nat:modCore-eq-mod n m
  = letFun#zz
    {#0 (Nat:modCore n m) (Nat:mod n m)}
    {λ (_ : #0 (Nat:modCore n m) (Nat:mod n m)) → #0 (Nat:modCore n m) (Nat:mod n m)}
    (Nat:modCore-eq-mod:match-1
      (λ (n$ : Nat) → λ (m$ : Nat) → #0 (Nat:modCore n$ m$) (Nat:mod n$ m$))
      n
      m
      (λ (x$ : Nat) →
        Eq:mpr#z
          {#0 (#154 x$) (#155 x$)}
          {#0
            (#152
              (And (#130 x$) (#99 x$ #4))
              {{instDecidableAnd {#130 x$} {#99 x$ #4} {{#153 x$}} {{Nat:decLe x$ #4}}}}
              (Nat:modCore (#157 x$) x$)
              #4)
            (#155 x$)}
          (id#z
            {#11
              (#0 (#154 x$) (#155 x$))
              (#0
                (#152
                  (And (#130 x$) (#99 x$ #4))
                  {{instDecidableAnd {#130 x$} {#99 x$ #4} {{#153 x$}} {{Nat:decLe x$ #4}}}}
                  (Nat:modCore (#157 x$) x$)
                  #4)
                (#155 x$))}
            (#13
              {#154 x$}
              {#152
                (And (#130 x$) (#99 x$ #4))
                {{instDecidableAnd {#130 x$} {#99 x$ #4} {{#153 x$}} {{Nat:decLe x$ #4}}}}
                (Nat:modCore (#157 x$) x$)
                #4}
              (λ (-a : Nat) → #0 -a (#155 x$))
              (Nat:modCore:eq-1 #4 x$)))
          (if-neg#n {lone}
            {And (#130 x$) (#99 x$ #4)}
            {instDecidableAnd {#130 x$} {#99 x$ #4} {{#153 x$}} {{Nat:decLe x$ #4}}}
            (λ (x$1 : And (#130 x$) (#99 x$ #4)) →
              Nat:modCore-eq-mod:match-2
                x$
                (λ (_ : And (#130 x$) (#99 x$ #4)) → False)
                x$1
                (λ (hlt : #130 x$) → λ (hle : #99 x$ #4) → #140 (Nat:lt-of-lt-of-le {#4} {x$} {#4} hlt hle)))
            {Nat}
            {Nat:modCore (#157 x$) x$}
            {#4}))
      (λ (n$ : Nat) →
        λ (x$ : Nat) →
          Eq:mpr#z
            {#0 (Nat:modCore (#16 n$ #17) x$) (Nat:mod (#16 n$ #17) x$)}
            {#0
              (Nat:modCore (#16 n$ #17) x$)
              (#152 (#99 x$ (Nat:succ n$)) {{Nat:decLe x$ (Nat:succ n$)}} (Nat:modCore (Nat:succ n$) x$) (Nat:succ n$))}
            (id#z
              {#11
                (#0 (Nat:modCore (#16 n$ #17) x$) (Nat:mod (#16 n$ #17) x$))
                (#0
                  (Nat:modCore (#16 n$ #17) x$)
                  (#152 (#99 x$ (Nat:succ n$)) {{Nat:decLe x$ (Nat:succ n$)}} (Nat:modCore (Nat:succ n$) x$) (Nat:succ n$)))}
              (#13
                {Nat:mod (Nat:succ n$) x$}
                {#152 (#99 x$ (Nat:succ n$)) {{Nat:decLe x$ (Nat:succ n$)}} (Nat:modCore (Nat:succ n$) x$) (Nat:succ n$)}
                (λ (-a : Nat) → #0 (Nat:modCore (#16 n$ #17) x$) -a)
                (Nat:mod:eq-2 x$ n$)))
            (id#z
              {#0
                (Nat:modCore (#16 n$ #17) x$)
                (#152 (#99 x$ (Nat:succ n$)) {{Nat:decLe x$ (Nat:succ n$)}} (Nat:modCore (Nat:succ n$) x$) (Nat:succ n$))}
              (iteInduction#nz {lone}
                {Nat}
                {#99 x$ (#16 n$ #17)}
                {{Nat:decLe x$ (#16 n$ #17)}}
                {#0 (Nat:modCore (#16 n$ #17) x$)}
                {Nat:modCore (#16 n$ #17) x$}
                {#16 n$ #17}
                (λ (_ : #99 x$ (#16 n$ #17)) → #40 {Nat:modCore (#16 n$ #17) x$})
                (λ (h : Not (#99 x$ (#16 n$ #17))) →
                  Eq:mpr#z
                    {#0 (Nat:modCore (#16 n$ #17) x$) (#16 n$ #17)}
                    {#0
                      (#152
                        (And (#130 x$) (#99 x$ (#16 n$ #17)))
                        {{instDecidableAnd {#130 x$} {#99 x$ (#16 n$ #17)} {{#153 x$}} {{Nat:decLe x$ (#16 n$ #17)}}}}
                        (Nat:modCore (#135 (#16 n$ #17) x$) x$)
                        (#16 n$ #17))
                      (#16 n$ #17)}
                    (id#z
                      {#11
                        (#0 (Nat:modCore (#16 n$ #17) x$) (#16 n$ #17))
                        (#0
                          (#152
                            (And (#130 x$) (#99 x$ (#16 n$ #17)))
                            {{instDecidableAnd {#130 x$} {#99 x$ (#16 n$ #17)} {{#153 x$}} {{Nat:decLe x$ (#16 n$ #17)}}}}
                            (Nat:modCore (#135 (#16 n$ #17) x$) x$)
                            (#16 n$ #17))
                          (#16 n$ #17))}
                      (#13
                        {Nat:modCore (#16 n$ #17) x$}
                        {#152
                          (And (#130 x$) (#99 x$ (#16 n$ #17)))
                          {{instDecidableAnd {#130 x$} {#99 x$ (#16 n$ #17)} {{#153 x$}} {{Nat:decLe x$ (#16 n$ #17)}}}}
                          (Nat:modCore (#135 (#16 n$ #17) x$) x$)
                          (#16 n$ #17)}
                        (λ (-a : Nat) → #0 -a (#16 n$ #17))
                        (Nat:modCore:eq-1 (#16 n$ #17) x$)))
                    (if-neg#n {lone}
                      {And (#130 x$) (#99 x$ (#16 n$ #17))}
                      {instDecidableAnd {#130 x$} {#99 x$ (#16 n$ #17)} {{#153 x$}} {{Nat:decLe x$ (#16 n$ #17)}}}
                      (λ (x$1 : And (#130 x$) (#99 x$ (#16 n$ #17))) →
                        Nat:modCore-eq-mod:match-3
                          n$
                          x$
                          (λ (_ : And (#130 x$) (#99 x$ (#16 n$ #17))) → False)
                          x$1
                          (λ (_ : #130 x$) → λ (hle : #99 x$ (#16 n$ #17)) → h hle))
                      {Nat}
                      {Nat:modCore (#135 (#16 n$ #17) x$) x$}
                      {#16 n$ #17}))))))
    (λ (this : #0 (Nat:modCore n m) (Nat:mod n m)) → this)

--theorem
Nat:mod-eq :
  (x : Nat) →
    (y : Nat) →
      #0
        (#19 x y)
        (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} (#19 (#136 x y) y) x)
Nat:mod-eq x y
  = Eq:mpr#z
    {#0
      (#19 x y)
      (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} (#19 (#136 x y) y) x)}
    {#0
      (Nat:modCore x y)
      (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} (#19 (#136 x y) y) x)}
    (id#z
      {#11
        (#0
          (#19 x y)
          (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} (#19 (#136 x y) y) x))
        (#0
          (Nat:modCore x y)
          (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} (#19 (#136 x y) y) x))}
      (#13
        {#19 x y}
        {Nat:modCore x y}
        (λ (-a : Nat) →
          #0
            -a
            (#152
              (And (#130 y) (#31 y x))
              {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
              (#19 (#136 x y) y)
              x))
        (#15 {Nat:modCore x y} {#19 x y} (Nat:modCore-eq-mod x y))))
    (Eq:mpr#z
      {#0
        (Nat:modCore x y)
        (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} (#19 (#136 x y) y) x)}
      {#0
        (Nat:modCore x y)
        (#152
          (And (#130 y) (#31 y x))
          {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
          (Nat:modCore (#136 x y) y)
          x)}
      (id#z
        {#11
          (#0
            (Nat:modCore x y)
            (#152
              (And (#130 y) (#31 y x))
              {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
              (#19 (#136 x y) y)
              x))
          (#0
            (Nat:modCore x y)
            (#152
              (And (#130 y) (#31 y x))
              {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
              (Nat:modCore (#136 x y) y)
              x))}
        (#13
          {#19 (#136 x y) y}
          {Nat:modCore (#136 x y) y}
          (λ (-a : Nat) →
            #0
              (Nat:modCore x y)
              (#152 (And (#130 y) (#31 y x)) {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}} -a x))
          (#15 {Nat:modCore (#136 x y) y} {#19 (#136 x y) y} (Nat:modCore-eq-mod (#136 x y) y))))
      (Eq:mpr#z
        {#0
          (Nat:modCore x y)
          (#152
            (And (#130 y) (#31 y x))
            {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
            (Nat:modCore (#136 x y) y)
            x)}
        {#0
          (#152
            (And (#130 y) (#99 y x))
            {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
            (Nat:modCore (#135 x y) y)
            x)
          (#152
            (And (#130 y) (#31 y x))
            {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
            (Nat:modCore (#136 x y) y)
            x)}
        (id#z
          {#11
            (#0
              (Nat:modCore x y)
              (#152
                (And (#130 y) (#31 y x))
                {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
                (Nat:modCore (#136 x y) y)
                x))
            (#0
              (#152
                (And (#130 y) (#99 y x))
                {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
                (Nat:modCore (#135 x y) y)
                x)
              (#152
                (And (#130 y) (#31 y x))
                {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
                (Nat:modCore (#136 x y) y)
                x))}
          (#13
            {Nat:modCore x y}
            {#152
              (And (#130 y) (#99 y x))
              {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
              (Nat:modCore (#135 x y) y)
              x}
            (λ (-a : Nat) →
              #0
                -a
                (#152
                  (And (#130 y) (#31 y x))
                  {{instDecidableAnd {#130 y} {#31 y x} {{#153 y}} {{Nat:decLe y x}}}}
                  (Nat:modCore (#136 x y) y)
                  x))
            (Nat:modCore:eq-1 x y)))
        (#62
          (#152
            (And (#130 y) (#99 y x))
            {{instDecidableAnd {#130 y} {#99 y x} {{#153 y}} {{Nat:decLe y x}}}}
            (Nat:modCore (#135 x y) y)
            x))))

--theorem
Eq:subst#n : {u : Level} → {α : Set u} → {motive : α → Prop} → {a : α} → {b : α} → Eq#n {u} {α} a b → motive a → motive b
Eq:subst#n {u} {α} {motive} {a} {b} h₁ h₂ = Eq:ndrec#zn {u} {α} {a} {motive} h₂ {b} h₁

--theorem
Nat:lt-of-le-of-lt : {n : Nat} → {m : Nat} → {k : Nat} → #31 n m → #26 m k → #26 n k
Nat:lt-of-le-of-lt {n} {m} {k} h₁ h₂ = Nat:le-trans {Nat:succ n} {Nat:succ m} {k} (Nat:succ-le-succ {n} {m} h₁) h₂

--def
Nat:le-antisymm:match-1 :
  {n : Nat} →
    (motive : (m$ : Nat) → #31 n m$ → #31 m$ n → Prop) →
      (m$ : Nat) →
        (h₁$ : #31 n m$) →
          (h₂ : #31 m$ n) →
            ((h₂# : #31 n n) → motive n (Nat:le:refl {n}) h₂#) →
              ((m$1 : Nat) → (h : Nat:le n m$1) → (h₂# : #31 (Nat:succ m$1) n) → motive (Nat:succ m$1) (Nat:le:step {n} {m$1} h) h₂#) →
                motive m$ h₁$ h₂
Nat:le-antisymm:match-1 {n} motive m$ h₁$ h₂ h-1 h-2
  = (λ (h₁$1 : Nat:le n m$) →
    Nat:le:casesOn
      {n}
      {λ (a$ : Nat) → λ (x : Nat:le n a$) → #0 m$ a$ → HEq#z {#31 n m$} h₁$ {Nat:le n a$} x → motive m$ h₁$ h₂}
      {m$}
      h₁$1
      (λ (h$ : #0 m$ n) →
        #5
          {n}
          {λ (m$1 : Nat) →
            (h₁$2 : #31 n m$1) → (h₂# : #31 m$1 n) → HEq#z {#31 n m$1} h₁$2 {Nat:le n n} (Nat:le:refl {n}) → motive m$1 h₁$2 h₂#}
          (λ (h₁$2 : #31 n n) →
            λ (h₂# : #31 n n) →
              λ (h$1 : HEq#z {#31 n n} h₁$2 {Nat:le n n} (Nat:le:refl {n})) →
                Eq:ndrec#zz
                  {#31 n n}
                  {Nat:le:refl {n}}
                  {λ (h₁$3 : #31 n n) → motive n h₁$3 h₂#}
                  (h-1 h₂#)
                  {h₁$2}
                  (Eq:symm#z {#31 n n} {h₁$2} {Nat:le:refl {n}} (eq-of-heq#z {#31 n n} {h₁$2} {Nat:le:refl {n}} h$1)))
          {m$}
          (#15 {m$} {n} h$)
          h₁$
          h₂)
      (λ {m$1 : Nat} →
        λ (a$ : Nat:le n m$1) →
          λ (h$ : #0 m$ (Nat:succ m$1)) →
            #5
              {Nat:succ m$1}
              {λ (m$2 : Nat) →
                (h₁$2 : #31 n m$2) →
                  (h₂# : #31 m$2 n) → HEq#z {#31 n m$2} h₁$2 {Nat:le n (Nat:succ m$1)} (Nat:le:step {n} {m$1} a$) → motive m$2 h₁$2 h₂#}
              (λ (h₁$2 : #31 n (Nat:succ m$1)) →
                λ (h₂# : #31 (Nat:succ m$1) n) →
                  λ (h$1 : HEq#z {#31 n (Nat:succ m$1)} h₁$2 {Nat:le n (Nat:succ m$1)} (Nat:le:step {n} {m$1} a$)) →
                    Eq:ndrec#zz
                      {#31 n (Nat:succ m$1)}
                      {Nat:le:step {n} {m$1} a$}
                      {λ (h₁$3 : #31 n (Nat:succ m$1)) → motive (Nat:succ m$1) h₁$3 h₂#}
                      (h-2 m$1 a$ h₂#)
                      {h₁$2}
                      (Eq:symm#z
                        {#31 n (Nat:succ m$1)}
                        {h₁$2}
                        {Nat:le:step {n} {m$1} a$}
                        (eq-of-heq#z {#31 n (Nat:succ m$1)} {h₁$2} {Nat:le:step {n} {m$1} a$} h$1)))
              {m$}
              (#15 {m$} {Nat:succ m$1} h$)
              h₁$
              h₂))
    h₁$
    (#62 m$)
    (HEq:refl#z {#31 n m$} h₁$)

--theorem
Nat:le-antisymm : {n : Nat} → {m : Nat} → #31 n m → #31 m n → #0 n m
Nat:le-antisymm {n} {m} h₁ h₂
  = Nat:le-antisymm:match-1
    {n}
    (λ (m$ : Nat) → λ (_ : #31 n m$) → λ (_ : #31 m$ n) → #0 n m$)
    m
    h₁
    h₂
    (λ (_ : #31 n n) → #40 {n})
    (λ (m$ : Nat) →
      λ (h : Nat:le n m$) →
        λ (h₂# : #31 (Nat:succ m$) n) →
          absurd#z {#26 n n} {#0 n (Nat:succ m$)} (Nat:lt-of-le-of-lt {n} {m$} {n} h h₂#) (Nat:lt-irrefl n))

--theorem
Nat:le-step : {n : Nat} → {m : Nat} → #31 n m → #31 n (Nat:succ m)
Nat:le-step {n} {m} h = Nat:le:step {n} {m} h

--theorem
Nat:lt-trans : {n : Nat} → {m : Nat} → {k : Nat} → #26 n m → #26 m k → #26 n k
Nat:lt-trans {n} {m} {k} h₁ = Nat:le-trans {Nat:succ n} {Nat:succ m} {k} (Nat:le-step {Nat:succ n} {m} h₁)

--def
Nat:le-total:match-1 :
  (m : Nat) →
    (n : Nat) →
      (motive : Or (#26 m n) (#151 m n) → Prop) →
        (x$ : Or (#26 m n) (#151 m n)) →
          ((h : #26 m n) → motive (Or:inl {#26 m n} {#151 m n} h)) → ((h : #151 m n) → motive (Or:inr {#26 m n} {#151 m n} h)) → motive x$
Nat:le-total:match-1 m n motive x$ h-1 h-2
  = Or:casesOn
    {#26 m n}
    {#151 m n}
    {λ (x : Or (#26 m n) (#151 m n)) → motive x}
    x$
    (λ (h$ : #26 m n) → h-1 h$)
    (λ (h$ : #151 m n) → h-2 h$)

--theorem
Nat:not-le-of-gt : {n : Nat} → {m : Nat} → #150 n m → Not (#31 n m)
Nat:not-le-of-gt {n} {m} h h₁
  = Nat:le-total:match-1
    n
    m
    (λ (_ : Or (#26 n m) (#151 n m)) → False)
    (Nat:lt-or-ge n m)
    (λ (h₂ : #26 n m) → absurd#z {#26 m m} {False} (Nat:lt-trans {m} {n} {m} h h₂) (Nat:lt-irrefl m))
    (λ (h₂ : #151 n m) →
      letFun#zz
        {#0 n m}
        {λ (_ : #0 n m) → False}
        (Nat:le-antisymm {n} {m} h₁ h₂)
        (λ (Heq : #0 n m) → absurd#z {#26 m m} {False} (Eq:subst#n {lone} {Nat} {#26 m} {n} {m} Heq h) (Nat:lt-irrefl m)))

--theorem
Nat:mod-eq-of-lt : {a : Nat} → {b : Nat} → #26 a b → #0 (#19 a b) a
Nat:mod-eq-of-lt {a} {b} h
  = letFun#zz
    {#0
      (#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a)
      a}
    {λ
      (_ :
        #0
          (#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a)
          a) →
      #0 (#19 a b) a}
    (letFun#zz
      {Not (And (#130 b) (#31 b a))}
      {λ (_ : Not (And (#130 b) (#31 b a))) →
        #0
          (#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a)
          a}
      (λ (x$ : And (#130 b) (#31 b a)) →
        Nat:div-rec-lemma:match-1
          {a}
          {b}
          (λ (_ : And (#130 b) (#31 b a)) → False)
          x$
          (λ (_ : #130 b) → λ (h₁ : #31 b a) → absurd#z {#31 b a} {False} h₁ (Nat:not-le-of-gt {b} {a} h)))
      (λ (h' : Not (And (#130 b) (#31 b a))) →
        if-neg#n {lone}
          {And (#130 b) (#31 b a)}
          {instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}
          h'
          {Nat}
          {#19 (#136 a b) b}
          {a}))
    (λ
      (this :
        #0
          (#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a)
          a) →
      Eq:rec#zn {lone}
        {Nat}
        {#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a}
        {λ (x$ : Nat) →
          λ
            (_ :
              #0
                (#152
                  (And (#130 b) (#31 b a))
                  {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}}
                  (#19 (#136 a b) b)
                  a)
                x$) →
            #0 x$ a}
        this
        {#19 a b}
        (#15
          {#19 a b}
          {#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a}
          (Nat:mod-eq a b)))

--def
#164 : {a$ : Nat} → {motive : (a$1 : Nat) → #0 a$ a$1 → Prop} → motive a$ (#62 a$) → {a$1 : Nat} → (t : #0 a$ a$1) → motive a$1 t
#164 {a$} {motive} = Eq:rec#zn {lone} {Nat} {a$} {motive}

--theorem
if-pos#n :
  {u : Level} →
    {c : Prop} → {h : Decidable c} → c → {α : Set u} → {t : α} → {e : α} → Eq#n {u} {α} (ite#n {u} {α} c {{h}} t e) t
if-pos#n {u} {c} {h} hc {α} {t} {e}
  = if-pos:match-1
    {c}
    (λ (h$ : Decidable c) → Eq#n {u} {α} (ite#n {u} {α} c {{h$}} t e) t)
    h
    (λ (h$ : c) → rfl#n {u} {α} {ite#n {u} {α} c {{Decidable:isTrue {c} h$}} t e})
    (λ (hnc : Not c) → absurd#z {c} {Eq#n {u} {α} (ite#n {u} {α} c {{Decidable:isFalse {c} hnc}} t e) t} hc hnc)

--theorem
Nat:zero-lt-succ : (n : Nat) → #130 (Nat:succ n)
Nat:zero-lt-succ n = Nat:succ-le-succ {#4} {n} (Nat:zero-le n)

--theorem
Nat:succ-pos : (n : Nat) → #130 (Nat:succ n)
Nat:succ-pos n = Nat:zero-lt-succ n

--def
#165 : Set₁
#165 = Nat → Prop

--def
Nat:zero-add:match-1 : (motive : #165) → (x$ : Nat) → (Unit → motive #4) → ((n : Nat) → motive (Nat:succ n)) → motive x$
Nat:zero-add:match-1 motive x$ h-1 h-2 = Nat:casesOn#z {λ (x : Nat) → motive x} x$ (h-1 Unit:unit) (λ (n$ : Nat) → h-2 n$)

--theorem
Nat:eq-zero-or-pos : (n : Nat) → Or (#0 n #4) (#150 n #4)
Nat:eq-zero-or-pos x$
  = Nat:zero-add:match-1
    (λ (x$1 : Nat) → Or (#0 x$1 #4) (#150 x$1 #4))
    x$
    (λ (_ : Unit) → Or:inl {#69 #4} {#150 #4 #4} (#40 {#4}))
    (λ (n$ : Nat) → Or:inr {#0 (#16 n$ #17) #4} {#150 (#16 n$ #17) #4} (Nat:succ-pos n$))

--theorem
Nat:sub-zero : (n : Nat) → #0 (#136 n #4) n
Nat:sub-zero n = #40 {#136 n #4}

--def
Nat:mod-eq-sub-mod:match-1 :
  {b : Nat} →
    (motive : Or (#0 b #4) (#150 b #4) → Prop) →
      (x$ : Or (#0 b #4) (#150 b #4)) →
        ((h₁ : #0 b #4) → motive (Or:inl {#0 b #4} {#150 b #4} h₁)) →
          ((h₁ : #150 b #4) → motive (Or:inr {#0 b #4} {#150 b #4} h₁)) → motive x$
Nat:mod-eq-sub-mod:match-1 {b} motive x$ h-1 h-2
  = Or:casesOn
    {#0 b #4}
    {#150 b #4}
    {λ (x : Or (#0 b #4) (#150 b #4)) → motive x}
    x$
    (λ (h$ : #0 b #4) → h-1 h$)
    (λ (h$ : #150 b #4) → h-2 h$)

--theorem
Nat:mod-eq-sub-mod : {a : Nat} → {b : Nat} → #151 a b → #0 (#19 a b) (#19 (#136 a b) b)
Nat:mod-eq-sub-mod {a} {b} h
  = Nat:mod-eq-sub-mod:match-1
    {b}
    (λ (_ : Or (#0 b #4) (#150 b #4)) → #0 (#19 a b) (#19 (#136 a b) b))
    (Nat:eq-zero-or-pos b)
    (λ (h₁ : #0 b #4) →
      #164
        {#4}
        {λ (x$ : Nat) → λ (_ : #69 x$) → #0 (#19 a x$) (#19 (#136 a x$) x$)}
        (#164
          {a}
          {λ (x$ : Nat) → λ (_ : #0 a x$) → #0 (#19 a #4) (#19 x$ #4)}
          (#40 {#19 a #4})
          {#136 a #4}
          (#15 {#136 a #4} {a} (Nat:sub-zero a)))
        {b}
        (#15 {b} {#4} h₁))
    (λ (h₁ : #150 b #4) →
      #164
        {#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a}
        {λ (x$ : Nat) →
          λ
            (_ :
              #0
                (#152
                  (And (#130 b) (#31 b a))
                  {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}}
                  (#19 (#136 a b) b)
                  a)
                x$) →
            #0 x$ (#19 (#136 a b) b)}
        (if-pos#n {lone}
          {And (#130 b) (#31 b a)}
          {instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}
          (And:intro {#130 b} {#31 b a} h₁ h)
          {Nat}
          {#19 (#136 a b) b}
          {a})
        {#19 a b}
        (#15
          {#19 a b}
          {#152 (And (#130 b) (#31 b a)) {{instDecidableAnd {#130 b} {#31 b a} {{#153 b}} {{Nat:decLe b a}}}} (#19 (#136 a b) b) a}
          (Nat:mod-eq a b)))

--def
#166#z : Set₁
#166#z = Nat → Nat → Prop

--def
#167#z : Set₁
#167#z = Nat → Nat → Prop

--def
#168#z : Set₂
#168#z = Nat → Set₁

--def
#169#z : #168#z → Set₁
#169#z = PSigma#nn {lone} {lone} {Nat}

--def
#170#z : {β : #168#z} → (fst : Nat) → β fst → #169#z β
#170#z {β} = PSigma:mk#nn {lone} {lone} {Nat} {β}

--record 2 2->2 0 2
record PSigma#zz {α : Prop} (β : α → Prop) : Set₁ where
  constructor PSigma:mk#zz
  field
    fst : α
    snd : β fst

--def
#171#z :
  {β : #168#z} → {motive : #169#z β → Set₁} → (t : #169#z β) → ((fst : Nat) → (snd : β fst) → motive (#170#z {β} fst snd)) → motive t
#171#z {β} {motive} = PSigma:casesOn#nnn {lone} {lone} {lone} {Nat} {β} {motive}

--def
#172 : WellFoundedRelation#n {lone} Nat
#172 = instWellFoundedRelationOfSizeOf#n {lone} {Nat} {{instSizeOfNat}}

--recursor 2->2 0->0 1 1
PSigma:rec#znn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {β : α → Set v} →
        {motive : PSigma#nn {u} {v} {α} β → Prop} →
          ((fst : α) → (snd : β fst) → motive (PSigma:mk#nn {u} {v} {α} {β} fst snd)) → (t : PSigma#nn {u} {v} {α} β) → motive t
PSigma:rec#znn {u} {v} {α} {β} {motive} mk (PSigma:mk#nn fst snd) = mk fst snd

--def
PSigma:casesOn#znn :
  {u : Level} → {v : Level} →
    {α : Set u} →
      {β : α → Set v} →
        {motive : PSigma#nn {u} {v} {α} β → Prop} →
          (t : PSigma#nn {u} {v} {α} β) → ((fst : α) → (snd : β fst) → motive (PSigma:mk#nn {u} {v} {α} {β} fst snd)) → motive t
PSigma:casesOn#znn {u} {v} {α} {β} {motive} t mk
  = PSigma:rec#znn {u} {v} {α} {β} {motive} (λ (fst : α) → λ (snd : β fst) → mk fst snd) t

--def
#173#z :
  {β : #168#z} → {motive : #169#z β → Prop} → (t : #169#z β) → ((fst : Nat) → (snd : β fst) → motive (#170#z {β} fst snd)) → motive t
#173#z {β} {motive} = PSigma:casesOn#znn {lone} {lone} {Nat} {β} {motive}

--def
dite#z : {α : Prop} → (c : Prop) → {{Decidable c}} → (c → α) → (Not c → α) → α
dite#z {α} c {{h}} t e = Decidable:casesOn#z {c} {λ (_ : Decidable c) → α} h e t

--recursor 2->2 0->0 1 1
PSigma:rec#zzz :
  {α : Prop} →
    {β : α → Prop} →
      {motive : PSigma#zz {α} β → Prop} →
        ((fst : α) → (snd : β fst) → motive (PSigma:mk#zz {α} {β} fst snd)) → (t : PSigma#zz {α} β) → motive t
PSigma:rec#zzz {α} {β} {motive} mk (PSigma:mk#zz fst snd) = mk fst snd

--def
PSigma:casesOn#zzz :
  {α : Prop} →
    {β : α → Prop} →
      {motive : PSigma#zz {α} β → Prop} →
        (t : PSigma#zz {α} β) → ((fst : α) → (snd : β fst) → motive (PSigma:mk#zz {α} {β} fst snd)) → motive t
PSigma:casesOn#zzz {α} {β} {motive} t mk = PSigma:rec#zzz {α} {β} {motive} (λ (fst : α) → λ (snd : β fst) → mk fst snd) t

--recursor 2->2 0->0 1 1
PSigma:rec#nzz :
  {u-1 : Level} →
    {α : Prop} →
      {β : α → Prop} →
        {motive : PSigma#zz {α} β → Set u-1} →
          ((fst : α) → (snd : β fst) → motive (PSigma:mk#zz {α} {β} fst snd)) → (t : PSigma#zz {α} β) → motive t
PSigma:rec#nzz {u-1} {α} {β} {motive} mk (PSigma:mk#zz fst snd) = mk fst snd

--def
PSigma:casesOn#nzz :
  {u-1 : Level} →
    {α : Prop} →
      {β : α → Prop} →
        {motive : PSigma#zz {α} β → Set u-1} →
          (t : PSigma#zz {α} β) → ((fst : α) → (snd : β fst) → motive (PSigma:mk#zz {α} {β} fst snd)) → motive t
PSigma:casesOn#nzz {u-1} {α} {β} {motive} t mk = PSigma:rec#nzz {u-1} {α} {β} {motive} (λ (fst : α) → λ (snd : β fst) → mk fst snd) t

--def
WellFounded:fixF#nz :
  {u : Level} →
    {α : Set u} →
      {r : α → α → Prop} → {C : α → Prop} → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → Acc#n {u} {α} r x → C x
WellFounded:fixF#nz {u} {α} {r} {C} F x a
  = Acc:rec#zn {u}
    {α}
    {r}
    {λ (x# : α) → λ (_ : Acc#n {u} {α} r x#) → C x#}
    (λ (x₁ : α) → λ (_ : (y : α) → r y x₁ → Acc#n {u} {α} r y) → λ (ih : (y : α) → r y x₁ → C y) → F x₁ ih)
    {x}
    a

--def
WellFounded:fix#nz :
  {u : Level} →
    {α : Set u} →
      {C : α → Prop} → {r : α → α → Prop} → WellFounded#n {u} {α} r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x
WellFounded:fix#nz {u} {α} {C} {r} hwf F x = WellFounded:fixF#nz {u} {α} {r} {C} F x (WellFounded:apply#n {u} {α} {r} hwf x)

--def
#174#z : Set₁
#174#z = Nat → Nat → Prop

--def
#175#z : Set₂
#175#z = Nat → Set₁

--def
#176#z : #175#z → Set₁
#176#z = PSigma#nn {lone} {lone} {Nat}

--def
#177#z :
  {β : #175#z} →
    {motive : #176#z β → Set₁} →
      (t : #176#z β) → ((fst : Nat) → (snd : β fst) → motive (PSigma:mk#nn {lone} {lone} {Nat} {β} fst snd)) → motive t
#177#z {β} {motive} = PSigma:casesOn#nnn {lone} {lone} {lone} {Nat} {β} {motive}

--theorem
Nat:div:inductionOn:-unary:proof-1#z :
  {motive : #174#z} →
    WellFounded#n {lone}
      {#176#z
        (λ (_ : Nat) →
          #176#z
            (λ (_ : Nat) →
              PSigma#zz
                {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                  (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))}
      (WellFoundedRelation#n.rel {lone}
        (invImage#nn {lone} {lone}
          {#176#z
            (λ (_ : Nat) →
              #176#z
                (λ (_ : Nat) →
                  PSigma#zz
                    {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                    (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                      (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))}
          {Nat}
          (λ
            (x$ :
              #176#z
                (λ (_ : Nat) →
                  #176#z
                    (λ (_ : Nat) →
                      PSigma#zz
                        {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                        (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                          (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
            #177#z
              {λ (_ : Nat) →
                #176#z
                  (λ (_ : Nat) →
                    PSigma#zz
                      {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                      (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                        (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y))}
              {λ
                (_ :
                  #176#z
                    (λ (_ : Nat) →
                      #176#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                            (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                              (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
                Nat}
              x$
              (λ (x : Nat) →
                λ
                  (y :
                    #176#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                          (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                            (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y))) →
                  #177#z
                    {λ (_ : Nat) →
                      PSigma#zz
                        {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                        (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                          (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
                    {λ
                      (_ :
                        #176#z
                          (λ (_ : Nat) →
                            PSigma#zz
                              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))) →
                      Nat}
                    y
                    (λ (_ : Nat) →
                      λ
                        (ind :
                          PSigma#zz
                            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)) →
                        PSigma:casesOn#nzz {lone}
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
                          {λ
                            (_ :
                              PSigma#zz
                                {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                                (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                  (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)) →
                            Nat}
                          ind
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            λ (_ : (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#) → x))))
          #172))
Nat:div:inductionOn:-unary:proof-1#z {motive}
  = WellFoundedRelation#n.wf {lone}
    (invImage#nn {lone} {lone}
      {#176#z
        (λ (_ : Nat) →
          #176#z
            (λ (_ : Nat) →
              PSigma#zz
                {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                  (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))}
      {Nat}
      (λ
        (x$ :
          #176#z
            (λ (_ : Nat) →
              #176#z
                (λ (_ : Nat) →
                  PSigma#zz
                    {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                    (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                      (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
        #177#z
          {λ (_ : Nat) →
            #176#z
              (λ (_ : Nat) →
                PSigma#zz
                  {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                  (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                    (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y))}
          {λ
            (_ :
              #176#z
                (λ (_ : Nat) →
                  #176#z
                    (λ (_ : Nat) →
                      PSigma#zz
                        {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                        (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                          (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
            Nat}
          x$
          (λ (x : Nat) →
            λ
              (y :
                #176#z
                  (λ (_ : Nat) →
                    PSigma#zz
                      {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                      (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                        (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y))) →
              #177#z
                {λ (_ : Nat) →
                  PSigma#zz
                    {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                    (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                      (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
                {λ
                  (_ :
                    #176#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))) →
                  Nat}
                y
                (λ (_ : Nat) →
                  λ
                    (ind :
                      PSigma#zz
                        {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                        (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                          (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)) →
                    PSigma:casesOn#nzz {lone}
                      {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                      {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                        (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
                      {λ
                        (_ :
                          PSigma#zz
                            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)) →
                        Nat}
                      ind
                      (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                        λ (_ : (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#) → x))))
      #172)

--def
#178#z : {β : #175#z} → (fst : Nat) → β fst → #176#z β
#178#z {β} = PSigma:mk#nn {lone} {lone} {Nat} {β}

--theorem
Nat:div:inductionOn:-unary:proof-2#z :
  {motive : #174#z} →
    (x : Nat) →
      (y : Nat) →
        (ind : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
          (base : (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#) →
            And (#130 y) (#31 y x) →
              WellFoundedRelation#n.rel {lone}
                (invImage#nn {lone} {lone}
                  {#176#z
                    (λ (_ : Nat) →
                      #176#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))}
                  {Nat}
                  (λ
                    (x$ :
                      #176#z
                        (λ (_ : Nat) →
                          #176#z
                            (λ (_ : Nat) →
                              PSigma#zz
                                {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                                (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                  (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
                    #177#z
                      {λ (_ : Nat) →
                        #176#z
                          (λ (_ : Nat) →
                            PSigma#zz
                              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
                      {λ
                        (_ :
                          #176#z
                            (λ (_ : Nat) →
                              #176#z
                                (λ (_ : Nat) →
                                  PSigma#zz
                                    {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                                    (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                      (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
                        Nat}
                      x$
                      (λ (x# : Nat) →
                        λ
                          (y# :
                            #176#z
                              (λ (_ : Nat) →
                                PSigma#zz
                                  {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                                  (λ
                                    (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                                    (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#))) →
                          #177#z
                            {λ (_ : Nat) →
                              PSigma#zz
                                {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                (λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                            {λ
                              (_ :
                                #176#z
                                  (λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))) →
                              Nat}
                            y#
                            (λ (_ : Nat) →
                              λ
                                (ind# :
                                  PSigma#zz
                                    {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                    (λ
                                      (_ :
                                        (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                      (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                                PSigma:casesOn#nzz {lone}
                                  {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                  {λ
                                    (_ :
                                      (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                    (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1}
                                  {λ
                                    (_ :
                                      PSigma#zz
                                        {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                        (λ
                                          (_ :
                                            (x#1 : Nat) →
                                              (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                          (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                                    Nat}
                                  ind#
                                  (λ
                                    (_ :
                                      (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                    λ (_ : (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1) → x#))))
                  #172)
                (#178#z
                  {λ (_ : Nat) →
                    #176#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
                  (#136 x y)
                  (#178#z
                    {λ (_ : Nat) →
                      PSigma#zz
                        {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                        (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                          (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
                    y
                    (PSigma:mk#zz
                      {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                      {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                        (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
                      ind
                      base)))
                (#178#z
                  {λ (_ : Nat) →
                    #176#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
                  x
                  (#178#z
                    {λ (_ : Nat) →
                      PSigma#zz
                        {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                        (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                          (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
                    y
                    (PSigma:mk#zz
                      {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                      {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                        (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
                      ind
                      base)))
Nat:div:inductionOn:-unary:proof-2#z {motive} x y ind base h
  = id#z
    {WellFoundedRelation#n.rel {lone}
      (invImage#nn {lone} {lone}
        {#176#z
          (λ (_ : Nat) →
            #176#z
              (λ (_ : Nat) →
                PSigma#zz
                  {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                  (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                    (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))}
        {Nat}
        (λ
          (x$ :
            #176#z
              (λ (_ : Nat) →
                #176#z
                  (λ (_ : Nat) →
                    PSigma#zz
                      {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                      (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                        (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
          #177#z
            {λ (_ : Nat) →
              #176#z
                (λ (_ : Nat) →
                  PSigma#zz
                    {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                    (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                      (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
            {λ
              (_ :
                #176#z
                  (λ (_ : Nat) →
                    #176#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
              Nat}
            x$
            (λ (x# : Nat) →
              λ
                (y# :
                  #176#z
                    (λ (_ : Nat) →
                      PSigma#zz
                        {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                        (λ (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                          (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#))) →
                #177#z
                  {λ (_ : Nat) →
                    PSigma#zz
                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                      (λ (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                  {λ
                    (_ :
                      #176#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                            (λ
                              (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                              (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))) →
                    Nat}
                  y#
                  (λ (_ : Nat) →
                    λ
                      (ind# :
                        PSigma#zz
                          {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                          (λ (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                            (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                      PSigma:casesOn#nzz {lone}
                        {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                        {λ (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                          (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1}
                        {λ
                          (_ :
                            PSigma#zz
                              {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                              (λ
                                (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                          Nat}
                        ind#
                        (λ (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                          λ (_ : (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1) → x#))))
        #172)
      (#178#z
        {λ (_ : Nat) →
          #176#z
            (λ (_ : Nat) →
              PSigma#zz
                {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                  (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
        (#136 x y)
        (#178#z
          {λ (_ : Nat) →
            PSigma#zz
              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
          y
          (PSigma:mk#zz
            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
            {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
            ind
            base)))
      (#178#z
        {λ (_ : Nat) →
          #176#z
            (λ (_ : Nat) →
              PSigma#zz
                {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                  (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
        x
        (#178#z
          {λ (_ : Nat) →
            PSigma#zz
              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
          y
          (PSigma:mk#zz
            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
            {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
            ind
            base)))}
    (Nat:div-rec-lemma {x} {y} h)

--def
Nat:div:inductionOn:-unary#z :
  {motive : #167#z} →
    (x :
      #169#z
        (λ (_ : Nat) →
          #169#z
            (λ (_ : Nat) →
              PSigma#zz
                {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                  (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
      motive (PSigma#nn.fst {lone} {lone} x) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} x))
Nat:div:inductionOn:-unary#z {motive}
  = WellFounded:fix#nz {lone}
    {#169#z
      (λ (_ : Nat) →
        #169#z
          (λ (_ : Nat) →
            PSigma#zz
              {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
              (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))}
    {λ
      (x :
        #169#z
          (λ (_ : Nat) →
            #169#z
              (λ (_ : Nat) →
                PSigma#zz
                  {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                  (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                    (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
      motive (PSigma#nn.fst {lone} {lone} x) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} x))}
    {WellFoundedRelation#n.rel {lone}
      (invImage#nn {lone} {lone}
        {#169#z
          (λ (_ : Nat) →
            #169#z
              (λ (_ : Nat) →
                PSigma#zz
                  {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                  (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                    (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))}
        {Nat}
        (λ
          (x$ :
            #169#z
              (λ (_ : Nat) →
                #169#z
                  (λ (_ : Nat) →
                    PSigma#zz
                      {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                      (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                        (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
          #171#z
            {λ (_ : Nat) →
              #169#z
                (λ (_ : Nat) →
                  PSigma#zz
                    {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                    (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                      (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y))}
            {λ
              (_ :
                #169#z
                  (λ (_ : Nat) →
                    #169#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                          (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                            (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
              Nat}
            x$
            (λ (x : Nat) →
              λ
                (y :
                  #169#z
                    (λ (_ : Nat) →
                      PSigma#zz
                        {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                        (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                          (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y))) →
                #171#z
                  {λ (_ : Nat) →
                    PSigma#zz
                      {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                      (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                        (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
                  {λ
                    (_ :
                      #169#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))) →
                    Nat}
                  y
                  (λ (_ : Nat) →
                    λ
                      (ind :
                        PSigma#zz
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)) →
                      PSigma:casesOn#nzz {lone}
                        {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                        {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                          (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
                        {λ
                          (_ :
                            PSigma#zz
                              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)) →
                          Nat}
                        ind
                        (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                          λ (_ : (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#) → x))))
        #172)}
    (Nat:div:inductionOn:-unary:proof-1#z {motive})
    (λ
      (x :
        #169#z
          (λ (_ : Nat) →
            #169#z
              (λ (_ : Nat) →
                PSigma#zz
                  {(x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y}
                  (λ (_ : (x : Nat) → (y : Nat) → And (#130 y) (#31 y x) → motive (#136 x y) y → motive x y) →
                    (x : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x)) → motive x y)))) →
      λ
        (a$ :
          (y :
            #169#z
              (λ (_ : Nat) →
                #169#z
                  (λ (_ : Nat) →
                    PSigma#zz
                      {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                      (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                        (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y)))) →
            WellFoundedRelation#n.rel {lone}
              (invImage#nn {lone} {lone}
                {#169#z
                  (λ (_ : Nat) →
                    #169#z
                      (λ (_ : Nat) →
                        PSigma#zz
                          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                          (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))}
                {Nat}
                (λ
                  (x$ :
                    #169#z
                      (λ (_ : Nat) →
                        #169#z
                          (λ (_ : Nat) →
                            PSigma#zz
                              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
                  #171#z
                    {λ (_ : Nat) →
                      #169#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
                    {λ
                      (_ :
                        #169#z
                          (λ (_ : Nat) →
                            #169#z
                              (λ (_ : Nat) →
                                PSigma#zz
                                  {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                                  (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                    (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
                      Nat}
                    x$
                    (λ (x# : Nat) →
                      λ
                        (y# :
                          #169#z
                            (λ (_ : Nat) →
                              PSigma#zz
                                {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                                (λ (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                                  (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#))) →
                        #171#z
                          {λ (_ : Nat) →
                            PSigma#zz
                              {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                              (λ
                                (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                          {λ
                            (_ :
                              #169#z
                                (λ (_ : Nat) →
                                  PSigma#zz
                                    {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                    (λ
                                      (_ :
                                        (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                      (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))) →
                            Nat}
                          y#
                          (λ (_ : Nat) →
                            λ
                              (ind :
                                PSigma#zz
                                  {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                  (λ
                                    (_ :
                                      (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                    (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                              PSigma:casesOn#nzz {lone}
                                {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                {λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1}
                                {λ
                                  (_ :
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                                  Nat}
                                ind
                                (λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  λ (_ : (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1) → x#))))
                #172)
              y
              x →
              motive (PSigma#nn.fst {lone} {lone} y) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y))) →
        #173#z
          {λ (_ : Nat) →
            #169#z
              (λ (_ : Nat) →
                PSigma#zz
                  {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                  (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                    (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y))}
          {λ
            (-x :
              #169#z
                (λ (_ : Nat) →
                  #169#z
                    (λ (_ : Nat) →
                      PSigma#zz
                        {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                        (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                          (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y)))) →
            ((y :
              #169#z
                (λ (_ : Nat) →
                  #169#z
                    (λ (_ : Nat) →
                      PSigma#zz
                        {(x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y}
                        (λ (_ : (x# : Nat) → (y : Nat) → And (#130 y) (#31 y x#) → motive (#136 x# y) y → motive x# y) →
                          (x# : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#)) → motive x# y)))) →
              WellFoundedRelation#n.rel {lone}
                (invImage#nn {lone} {lone}
                  {#169#z
                    (λ (_ : Nat) →
                      #169#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))}
                  {Nat}
                  (λ
                    (x$ :
                      #169#z
                        (λ (_ : Nat) →
                          #169#z
                            (λ (_ : Nat) →
                              PSigma#zz
                                {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                                (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                  (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
                    #171#z
                      {λ (_ : Nat) →
                        #169#z
                          (λ (_ : Nat) →
                            PSigma#zz
                              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
                      {λ
                        (_ :
                          #169#z
                            (λ (_ : Nat) →
                              #169#z
                                (λ (_ : Nat) →
                                  PSigma#zz
                                    {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
                                    (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                                      (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)))) →
                        Nat}
                      x$
                      (λ (x# : Nat) →
                        λ
                          (y# :
                            #169#z
                              (λ (_ : Nat) →
                                PSigma#zz
                                  {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                                  (λ
                                    (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                                    (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#))) →
                          #171#z
                            {λ (_ : Nat) →
                              PSigma#zz
                                {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                (λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                            {λ
                              (_ :
                                #169#z
                                  (λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))) →
                              Nat}
                            y#
                            (λ (_ : Nat) →
                              λ
                                (ind :
                                  PSigma#zz
                                    {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                    (λ
                                      (_ :
                                        (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                      (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                                PSigma:casesOn#nzz {lone}
                                  {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                  {λ
                                    (_ :
                                      (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                    (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1}
                                  {λ
                                    (_ :
                                      PSigma#zz
                                        {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                        (λ
                                          (_ :
                                            (x#1 : Nat) →
                                              (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                          (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                                    Nat}
                                  ind
                                  (λ
                                    (_ :
                                      (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                    λ (_ : (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1) → x#))))
                  #172)
                y
                -x →
                motive (PSigma#nn.fst {lone} {lone} y) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y))) →
              motive (PSigma#nn.fst {lone} {lone} -x) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} -x))}
          x
          (λ (x# : Nat) →
            λ
              (y :
                #169#z
                  (λ (_ : Nat) →
                    PSigma#zz
                      {(x#1 : Nat) → (y : Nat) → And (#130 y) (#31 y x#1) → motive (#136 x#1 y) y → motive x#1 y}
                      (λ (_ : (x#1 : Nat) → (y : Nat) → And (#130 y) (#31 y x#1) → motive (#136 x#1 y) y → motive x#1 y) →
                        (x#1 : Nat) → (y : Nat) → Not (And (#130 y) (#31 y x#1)) → motive x#1 y))) →
              λ
                (a$1 :
                  (y# :
                    #169#z
                      (λ (_ : Nat) →
                        #169#z
                          (λ (_ : Nat) →
                            PSigma#zz
                              {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                              (λ (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                                (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#)))) →
                    WellFoundedRelation#n.rel {lone}
                      (invImage#nn {lone} {lone}
                        {#169#z
                          (λ (_ : Nat) →
                            #169#z
                              (λ (_ : Nat) →
                                PSigma#zz
                                  {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                  (λ
                                    (_ :
                                      (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                    (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))}
                        {Nat}
                        (λ
                          (x$ :
                            #169#z
                              (λ (_ : Nat) →
                                #169#z
                                  (λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))) →
                          #171#z
                            {λ (_ : Nat) →
                              #169#z
                                (λ (_ : Nat) →
                                  PSigma#zz
                                    {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                    (λ
                                      (_ :
                                        (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                      (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                            {λ
                              (_ :
                                #169#z
                                  (λ (_ : Nat) →
                                    #169#z
                                      (λ (_ : Nat) →
                                        PSigma#zz
                                          {(x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                          (λ
                                            (_ :
                                              (x#1 : Nat) →
                                                (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                            (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))) →
                              Nat}
                            x$
                            (λ (x#1 : Nat) →
                              λ
                                (y#1 :
                                  #169#z
                                    (λ (_ : Nat) →
                                      PSigma#zz
                                        {(x#2 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#2) → motive (#136 x#2 y#1) y#1 → motive x#2 y#1}
                                        (λ
                                          (_ :
                                            (x#2 : Nat) →
                                              (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#2) → motive (#136 x#2 y#1) y#1 → motive x#2 y#1) →
                                          (x#2 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#2)) → motive x#2 y#1))) →
                                #171#z
                                  {λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#2 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                      (λ
                                        (_ :
                                          (x#2 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                        (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2)}
                                  {λ
                                    (_ :
                                      #169#z
                                        (λ (_ : Nat) →
                                          PSigma#zz
                                            {(x#2 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                            (λ
                                              (_ :
                                                (x#2 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                              (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2))) →
                                    Nat}
                                  y#1
                                  (λ (_ : Nat) →
                                    λ
                                      (ind :
                                        PSigma#zz
                                          {(x#2 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                          (λ
                                            (_ :
                                              (x#2 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                            (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2)) →
                                      PSigma:casesOn#nzz {lone}
                                        {(x#2 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                        {λ
                                          (_ :
                                            (x#2 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                          (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2}
                                        {λ
                                          (_ :
                                            PSigma#zz
                                              {(x#2 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                              (λ
                                                (_ :
                                                  (x#2 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                                (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2)) →
                                          Nat}
                                        ind
                                        (λ
                                          (_ :
                                            (x#2 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                          λ (_ : (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2) → x#1))))
                        #172)
                      y#
                      (#170#z
                        {λ (_ : Nat) →
                          #169#z
                            (λ (_ : Nat) →
                              PSigma#zz
                                {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                (λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                        x#
                        y) →
                      motive (PSigma#nn.fst {lone} {lone} y#) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y#))) →
                #173#z
                  {λ (_ : Nat) →
                    PSigma#zz
                      {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                      (λ (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                        (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#)}
                  {λ
                    (y# :
                      #169#z
                        (λ (_ : Nat) →
                          PSigma#zz
                            {(x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#}
                            (λ (_ : (x#1 : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#1) → motive (#136 x#1 y#) y# → motive x#1 y#) →
                              (x#1 : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#1)) → motive x#1 y#))) →
                    ((y#1 :
                      #169#z
                        (λ (_ : Nat) →
                          #169#z
                            (λ (_ : Nat) →
                              PSigma#zz
                                {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                (λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))) →
                      WellFoundedRelation#n.rel {lone}
                        (invImage#nn {lone} {lone}
                          {#169#z
                            (λ (_ : Nat) →
                              #169#z
                                (λ (_ : Nat) →
                                  PSigma#zz
                                    {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                    (λ
                                      (_ :
                                        (x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                      (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))}
                          {Nat}
                          (λ
                            (x$ :
                              #169#z
                                (λ (_ : Nat) →
                                  #169#z
                                    (λ (_ : Nat) →
                                      PSigma#zz
                                        {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                        (λ
                                          (_ :
                                            (x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                          (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                            #171#z
                              {λ (_ : Nat) →
                                #169#z
                                  (λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                        (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                              {λ
                                (_ :
                                  #169#z
                                    (λ (_ : Nat) →
                                      #169#z
                                        (λ (_ : Nat) →
                                          PSigma#zz
                                            {(x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                            (λ
                                              (_ :
                                                (x#1 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                              (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                Nat}
                              x$
                              (λ (x#1 : Nat) →
                                λ
                                  (y#2 :
                                    #169#z
                                      (λ (_ : Nat) →
                                        PSigma#zz
                                          {(x#2 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                          (λ
                                            (_ :
                                              (x#2 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                            (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2))) →
                                  #171#z
                                    {λ (_ : Nat) →
                                      PSigma#zz
                                        {(x#2 : Nat) → (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                        (λ
                                          (_ :
                                            (x#2 : Nat) →
                                              (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                          (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)}
                                    {λ
                                      (_ :
                                        #169#z
                                          (λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#2 : Nat) →
                                                (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                              (λ
                                                (_ :
                                                  (x#2 : Nat) →
                                                    (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3))) →
                                      Nat}
                                    y#2
                                    (λ (_ : Nat) →
                                      λ
                                        (ind :
                                          PSigma#zz
                                            {(x#2 : Nat) →
                                              (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                            (λ
                                              (_ :
                                                (x#2 : Nat) →
                                                  (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                              (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                        PSigma:casesOn#nzz {lone}
                                          {(x#2 : Nat) →
                                            (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                          {λ
                                            (_ :
                                              (x#2 : Nat) →
                                                (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                            (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3}
                                          {λ
                                            (_ :
                                              PSigma#zz
                                                {(x#2 : Nat) →
                                                  (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                (λ
                                                  (_ :
                                                    (x#2 : Nat) →
                                                      (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                  (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                            Nat}
                                          ind
                                          (λ
                                            (_ :
                                              (x#2 : Nat) →
                                                (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                            λ (_ : (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3) → x#1))))
                          #172)
                        y#1
                        (#170#z
                          {λ (_ : Nat) →
                            #169#z
                              (λ (_ : Nat) →
                                PSigma#zz
                                  {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                  (λ
                                    (_ :
                                      (x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                    (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                          x#
                          y#) →
                        motive (PSigma#nn.fst {lone} {lone} y#1) (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y#1))) →
                      motive
                        (PSigma#nn.fst {lone} {lone}
                          (#170#z
                            {λ (_ : Nat) →
                              #169#z
                                (λ (_ : Nat) →
                                  PSigma#zz
                                    {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                    (λ
                                      (_ :
                                        (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                      (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                            x#
                            y#))
                        (PSigma#nn.fst {lone} {lone}
                          (PSigma#nn.snd {lone} {lone}
                            (#170#z
                              {λ (_ : Nat) →
                                #169#z
                                  (λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                              x#
                              y#)))}
                  y
                  (λ (y# : Nat) →
                    λ
                      (ind :
                        PSigma#zz
                          {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                          (λ (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                            (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                      λ
                        (a$2 :
                          (y#1 :
                            #169#z
                              (λ (_ : Nat) →
                                #169#z
                                  (λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                        (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))) →
                            WellFoundedRelation#n.rel {lone}
                              (invImage#nn {lone} {lone}
                                {#169#z
                                  (λ (_ : Nat) →
                                    #169#z
                                      (λ (_ : Nat) →
                                        PSigma#zz
                                          {(x#1 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                          (λ
                                            (_ :
                                              (x#1 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                            (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))}
                                {Nat}
                                (λ
                                  (x$ :
                                    #169#z
                                      (λ (_ : Nat) →
                                        #169#z
                                          (λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#1 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                              (λ
                                                (_ :
                                                  (x#1 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                  #171#z
                                    {λ (_ : Nat) →
                                      #169#z
                                        (λ (_ : Nat) →
                                          PSigma#zz
                                            {(x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                            (λ
                                              (_ :
                                                (x#1 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                              (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                                    {λ
                                      (_ :
                                        #169#z
                                          (λ (_ : Nat) →
                                            #169#z
                                              (λ (_ : Nat) →
                                                PSigma#zz
                                                  {(x#1 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                  (λ
                                                    (_ :
                                                      (x#1 : Nat) →
                                                        (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                    (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                      Nat}
                                    x$
                                    (λ (x#1 : Nat) →
                                      λ
                                        (y#2 :
                                          #169#z
                                            (λ (_ : Nat) →
                                              PSigma#zz
                                                {(x#2 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                                (λ
                                                  (_ :
                                                    (x#2 : Nat) →
                                                      (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                                  (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2))) →
                                        #171#z
                                          {λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#2 : Nat) →
                                                (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                              (λ
                                                (_ :
                                                  (x#2 : Nat) →
                                                    (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)}
                                          {λ
                                            (_ :
                                              #169#z
                                                (λ (_ : Nat) →
                                                  PSigma#zz
                                                    {(x#2 : Nat) →
                                                      (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                    (λ
                                                      (_ :
                                                        (x#2 : Nat) →
                                                          (y#3 : Nat) →
                                                            And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                      (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3))) →
                                            Nat}
                                          y#2
                                          (λ (_ : Nat) →
                                            λ
                                              (ind# :
                                                PSigma#zz
                                                  {(x#2 : Nat) →
                                                    (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                  (λ
                                                    (_ :
                                                      (x#2 : Nat) →
                                                        (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                    (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                              PSigma:casesOn#nzz {lone}
                                                {(x#2 : Nat) →
                                                  (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                {λ
                                                  (_ :
                                                    (x#2 : Nat) →
                                                      (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                  (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3}
                                                {λ
                                                  (_ :
                                                    PSigma#zz
                                                      {(x#2 : Nat) →
                                                        (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                      (λ
                                                        (_ :
                                                          (x#2 : Nat) →
                                                            (y#3 : Nat) →
                                                              And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                        (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                                  Nat}
                                                ind#
                                                (λ
                                                  (_ :
                                                    (x#2 : Nat) →
                                                      (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                  λ
                                                    (_ : (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3) →
                                                    x#1))))
                                #172)
                              y#1
                              (#170#z
                                {λ (_ : Nat) →
                                  #169#z
                                    (λ (_ : Nat) →
                                      PSigma#zz
                                        {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                        (λ
                                          (_ :
                                            (x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                          (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                                x#
                                (#170#z
                                  {λ (_ : Nat) →
                                    PSigma#zz
                                      {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                      (λ
                                        (_ :
                                          (x#1 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                        (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)}
                                  y#
                                  ind)) →
                              motive
                                (PSigma#nn.fst {lone} {lone} y#1)
                                (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y#1))) →
                        PSigma:casesOn#zzz
                          {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                          {λ (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                            (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1}
                          {λ
                            (ind# :
                              PSigma#zz
                                {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                (λ
                                  (_ : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)) →
                            ((y#1 :
                              #169#z
                                (λ (_ : Nat) →
                                  #169#z
                                    (λ (_ : Nat) →
                                      PSigma#zz
                                        {(x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                        (λ
                                          (_ :
                                            (x#1 : Nat) →
                                              (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                          (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))) →
                              WellFoundedRelation#n.rel {lone}
                                (invImage#nn {lone} {lone}
                                  {#169#z
                                    (λ (_ : Nat) →
                                      #169#z
                                        (λ (_ : Nat) →
                                          PSigma#zz
                                            {(x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                            (λ
                                              (_ :
                                                (x#1 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                              (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))}
                                  {Nat}
                                  (λ
                                    (x$ :
                                      #169#z
                                        (λ (_ : Nat) →
                                          #169#z
                                            (λ (_ : Nat) →
                                              PSigma#zz
                                                {(x#1 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                (λ
                                                  (_ :
                                                    (x#1 : Nat) →
                                                      (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                  (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                    #171#z
                                      {λ (_ : Nat) →
                                        #169#z
                                          (λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#1 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                              (λ
                                                (_ :
                                                  (x#1 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                                      {λ
                                        (_ :
                                          #169#z
                                            (λ (_ : Nat) →
                                              #169#z
                                                (λ (_ : Nat) →
                                                  PSigma#zz
                                                    {(x#1 : Nat) →
                                                      (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                    (λ
                                                      (_ :
                                                        (x#1 : Nat) →
                                                          (y#2 : Nat) →
                                                            And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                      (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                        Nat}
                                      x$
                                      (λ (x#1 : Nat) →
                                        λ
                                          (y#2 :
                                            #169#z
                                              (λ (_ : Nat) →
                                                PSigma#zz
                                                  {(x#2 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                                  (λ
                                                    (_ :
                                                      (x#2 : Nat) →
                                                        (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                                    (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2))) →
                                          #171#z
                                            {λ (_ : Nat) →
                                              PSigma#zz
                                                {(x#2 : Nat) →
                                                  (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                (λ
                                                  (_ :
                                                    (x#2 : Nat) →
                                                      (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                  (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)}
                                            {λ
                                              (_ :
                                                #169#z
                                                  (λ (_ : Nat) →
                                                    PSigma#zz
                                                      {(x#2 : Nat) →
                                                        (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                      (λ
                                                        (_ :
                                                          (x#2 : Nat) →
                                                            (y#3 : Nat) →
                                                              And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                        (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3))) →
                                              Nat}
                                            y#2
                                            (λ (_ : Nat) →
                                              λ
                                                (ind#1 :
                                                  PSigma#zz
                                                    {(x#2 : Nat) →
                                                      (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                    (λ
                                                      (_ :
                                                        (x#2 : Nat) →
                                                          (y#3 : Nat) →
                                                            And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                      (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                                PSigma:casesOn#nzz {lone}
                                                  {(x#2 : Nat) →
                                                    (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                  {λ
                                                    (_ :
                                                      (x#2 : Nat) →
                                                        (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                    (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3}
                                                  {λ
                                                    (_ :
                                                      PSigma#zz
                                                        {(x#2 : Nat) →
                                                          (y#3 : Nat) →
                                                            And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                        (λ
                                                          (_ :
                                                            (x#2 : Nat) →
                                                              (y#3 : Nat) →
                                                                And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                          (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                                    Nat}
                                                  ind#1
                                                  (λ
                                                    (_ :
                                                      (x#2 : Nat) →
                                                        (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                    λ
                                                      (_ : (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3) →
                                                      x#1))))
                                  #172)
                                y#1
                                (#170#z
                                  {λ (_ : Nat) →
                                    #169#z
                                      (λ (_ : Nat) →
                                        PSigma#zz
                                          {(x#1 : Nat) →
                                            (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                          (λ
                                            (_ :
                                              (x#1 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                            (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                                  x#
                                  (#170#z
                                    {λ (_ : Nat) →
                                      PSigma#zz
                                        {(x#1 : Nat) → (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                        (λ
                                          (_ :
                                            (x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                          (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)}
                                    y#
                                    ind#)) →
                                motive
                                  (PSigma#nn.fst {lone} {lone} y#1)
                                  (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y#1))) →
                              motive
                                (PSigma#nn.fst {lone} {lone}
                                  (#170#z
                                    {λ (_ : Nat) →
                                      #169#z
                                        (λ (_ : Nat) →
                                          PSigma#zz
                                            {(x#1 : Nat) →
                                              (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                            (λ
                                              (_ :
                                                (x#1 : Nat) →
                                                  (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                              (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                                    x#
                                    (#170#z
                                      {λ (_ : Nat) →
                                        PSigma#zz
                                          {(x#1 : Nat) →
                                            (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                          (λ
                                            (_ :
                                              (x#1 : Nat) →
                                                (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                            (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                                      y#
                                      ind#)))
                                (PSigma#nn.fst {lone} {lone}
                                  (PSigma#nn.snd {lone} {lone}
                                    (#170#z
                                      {λ (_ : Nat) →
                                        #169#z
                                          (λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#1 : Nat) →
                                                (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                              (λ
                                                (_ :
                                                  (x#1 : Nat) →
                                                    (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                                (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                                      x#
                                      (#170#z
                                        {λ (_ : Nat) →
                                          PSigma#zz
                                            {(x#1 : Nat) →
                                              (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                            (λ
                                              (_ :
                                                (x#1 : Nat) →
                                                  (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                              (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                                        y#
                                        ind#))))}
                          ind
                          (λ
                            (ind# : (x#1 : Nat) → (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                            λ (base : (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1) →
                              λ
                                (a$3 :
                                  (y#1 :
                                    #169#z
                                      (λ (_ : Nat) →
                                        #169#z
                                          (λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#1 : Nat) →
                                                (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                              (λ
                                                (_ :
                                                  (x#1 : Nat) →
                                                    (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                                (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)))) →
                                    WellFoundedRelation#n.rel {lone}
                                      (invImage#nn {lone} {lone}
                                        {#169#z
                                          (λ (_ : Nat) →
                                            #169#z
                                              (λ (_ : Nat) →
                                                PSigma#zz
                                                  {(x#1 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                  (λ
                                                    (_ :
                                                      (x#1 : Nat) →
                                                        (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                    (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))}
                                        {Nat}
                                        (λ
                                          (x$ :
                                            #169#z
                                              (λ (_ : Nat) →
                                                #169#z
                                                  (λ (_ : Nat) →
                                                    PSigma#zz
                                                      {(x#1 : Nat) →
                                                        (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                      (λ
                                                        (_ :
                                                          (x#1 : Nat) →
                                                            (y#2 : Nat) →
                                                              And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                        (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                          #171#z
                                            {λ (_ : Nat) →
                                              #169#z
                                                (λ (_ : Nat) →
                                                  PSigma#zz
                                                    {(x#1 : Nat) →
                                                      (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                    (λ
                                                      (_ :
                                                        (x#1 : Nat) →
                                                          (y#2 : Nat) →
                                                            And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                      (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                                            {λ
                                              (_ :
                                                #169#z
                                                  (λ (_ : Nat) →
                                                    #169#z
                                                      (λ (_ : Nat) →
                                                        PSigma#zz
                                                          {(x#1 : Nat) →
                                                            (y#2 : Nat) →
                                                              And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                          (λ
                                                            (_ :
                                                              (x#1 : Nat) →
                                                                (y#2 : Nat) →
                                                                  And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                            (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)))) →
                                              Nat}
                                            x$
                                            (λ (x#1 : Nat) →
                                              λ
                                                (y#2 :
                                                  #169#z
                                                    (λ (_ : Nat) →
                                                      PSigma#zz
                                                        {(x#2 : Nat) →
                                                          (y#2 : Nat) →
                                                            And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2}
                                                        (λ
                                                          (_ :
                                                            (x#2 : Nat) →
                                                              (y#2 : Nat) →
                                                                And (#130 y#2) (#31 y#2 x#2) → motive (#136 x#2 y#2) y#2 → motive x#2 y#2) →
                                                          (x#2 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#2)) → motive x#2 y#2))) →
                                                #171#z
                                                  {λ (_ : Nat) →
                                                    PSigma#zz
                                                      {(x#2 : Nat) →
                                                        (y#3 : Nat) → And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                      (λ
                                                        (_ :
                                                          (x#2 : Nat) →
                                                            (y#3 : Nat) →
                                                              And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                        (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)}
                                                  {λ
                                                    (_ :
                                                      #169#z
                                                        (λ (_ : Nat) →
                                                          PSigma#zz
                                                            {(x#2 : Nat) →
                                                              (y#3 : Nat) →
                                                                And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                            (λ
                                                              (_ :
                                                                (x#2 : Nat) →
                                                                  (y#3 : Nat) →
                                                                    And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                              (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3))) →
                                                    Nat}
                                                  y#2
                                                  (λ (_ : Nat) →
                                                    λ
                                                      (ind#1 :
                                                        PSigma#zz
                                                          {(x#2 : Nat) →
                                                            (y#3 : Nat) →
                                                              And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                          (λ
                                                            (_ :
                                                              (x#2 : Nat) →
                                                                (y#3 : Nat) →
                                                                  And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                            (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                                      PSigma:casesOn#nzz {lone}
                                                        {(x#2 : Nat) →
                                                          (y#3 : Nat) →
                                                            And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                        {λ
                                                          (_ :
                                                            (x#2 : Nat) →
                                                              (y#3 : Nat) →
                                                                And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                          (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3}
                                                        {λ
                                                          (_ :
                                                            PSigma#zz
                                                              {(x#2 : Nat) →
                                                                (y#3 : Nat) →
                                                                  And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3}
                                                              (λ
                                                                (_ :
                                                                  (x#2 : Nat) →
                                                                    (y#3 : Nat) →
                                                                      And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                                (x#2 : Nat) →
                                                                  (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3)) →
                                                          Nat}
                                                        ind#1
                                                        (λ
                                                          (_ :
                                                            (x#2 : Nat) →
                                                              (y#3 : Nat) →
                                                                And (#130 y#3) (#31 y#3 x#2) → motive (#136 x#2 y#3) y#3 → motive x#2 y#3) →
                                                          λ
                                                            (_ :
                                                              (x#2 : Nat) → (y#3 : Nat) → Not (And (#130 y#3) (#31 y#3 x#2)) → motive x#2 y#3) →
                                                            x#1))))
                                        #172)
                                      y#1
                                      (#170#z
                                        {λ (_ : Nat) →
                                          #169#z
                                            (λ (_ : Nat) →
                                              PSigma#zz
                                                {(x#1 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                                (λ
                                                  (_ :
                                                    (x#1 : Nat) →
                                                      (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                  (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2))}
                                        x#
                                        (#170#z
                                          {λ (_ : Nat) →
                                            PSigma#zz
                                              {(x#1 : Nat) →
                                                (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                              (λ
                                                (_ :
                                                  (x#1 : Nat) →
                                                    (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                                (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2)}
                                          y#
                                          (PSigma:mk#zz
                                            {(x#1 : Nat) →
                                              (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2}
                                            {λ
                                              (_ :
                                                (x#1 : Nat) →
                                                  (y#2 : Nat) → And (#130 y#2) (#31 y#2 x#1) → motive (#136 x#1 y#2) y#2 → motive x#1 y#2) →
                                              (x#1 : Nat) → (y#2 : Nat) → Not (And (#130 y#2) (#31 y#2 x#1)) → motive x#1 y#2}
                                            ind#
                                            base))) →
                                      motive
                                        (PSigma#nn.fst {lone} {lone} y#1)
                                        (PSigma#nn.fst {lone} {lone} (PSigma#nn.snd {lone} {lone} y#1))) →
                                dite#z
                                  {motive x# y#}
                                  (And (#130 y#) (#31 y# x#))
                                  {{instDecidableAnd {#130 y#} {#31 y# x#} {{#153 y#}} {{Nat:decLe y# x#}}}}
                                  (λ (h : And (#130 y#) (#31 y# x#)) →
                                    ind#
                                      x#
                                      y#
                                      h
                                      (a$3
                                        (#170#z
                                          {λ (_ : Nat) →
                                            #169#z
                                              (λ (_ : Nat) →
                                                PSigma#zz
                                                  {(x#1 : Nat) →
                                                    (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                                  (λ
                                                    (_ :
                                                      (x#1 : Nat) →
                                                        (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                                    (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1))}
                                          (#136 x# y#)
                                          (#170#z
                                            {λ (_ : Nat) →
                                              PSigma#zz
                                                {(x#1 : Nat) →
                                                  (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                                (λ
                                                  (_ :
                                                    (x#1 : Nat) →
                                                      (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                                  (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1)}
                                            y#
                                            (PSigma:mk#zz
                                              {(x#1 : Nat) →
                                                (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1}
                                              {λ
                                                (_ :
                                                  (x#1 : Nat) →
                                                    (y#1 : Nat) → And (#130 y#1) (#31 y#1 x#1) → motive (#136 x#1 y#1) y#1 → motive x#1 y#1) →
                                                (x#1 : Nat) → (y#1 : Nat) → Not (And (#130 y#1) (#31 y#1 x#1)) → motive x#1 y#1}
                                              ind#
                                              base)))
                                        (Nat:div:inductionOn:-unary:proof-2#z {motive} x# y# ind# base h)))
                                  (λ (h : Not (And (#130 y#) (#31 y# x#))) → base x# y# h))
                          a$2)
                  a$1)
          a$)

--def
Nat:div:inductionOn#z :
  {motive : #167#z} →
    (x : Nat) →
      (y : Nat) →
        ((x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
          ((x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#) → motive x y
Nat:div:inductionOn#z {motive} x y ind base
  = Nat:div:inductionOn:-unary#z
    {motive}
    (#170#z
      {λ (_ : Nat) →
        #169#z
          (λ (_ : Nat) →
            PSigma#zz
              {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
              (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
                (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#))}
      x
      (#170#z
        {λ (_ : Nat) →
          PSigma#zz
            {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
            (λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
              (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#)}
        y
        (PSigma:mk#zz
          {(x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#}
          {λ (_ : (x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
            (x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#}
          ind
          base)))

--def
Nat:mod:inductionOn#z :
  {motive : #166#z} →
    (x : Nat) →
      (y : Nat) →
        ((x# : Nat) → (y# : Nat) → And (#130 y#) (#31 y# x#) → motive (#136 x# y#) y# → motive x# y#) →
          ((x# : Nat) → (y# : Nat) → Not (And (#130 y#) (#31 y# x#)) → motive x# y#) → motive x y
Nat:mod:inductionOn#z {motive} x y ind base = Nat:div:inductionOn#z {motive} x y ind base

--def
Nat:mod-lt:match-1 :
  (x : Nat) →
    (y : Nat) →
      (motive : Or (Not (#130 y)) (Not (#31 y x)) → Prop) →
        (h₁$ : Or (Not (#130 y)) (Not (#31 y x))) →
          ((h₁ : Not (#130 y)) → motive (Or:inl {Not (#130 y)} {Not (#31 y x)} h₁)) →
            ((h₁ : Not (#31 y x)) → motive (Or:inr {Not (#130 y)} {Not (#31 y x)} h₁)) → motive h₁$
Nat:mod-lt:match-1 x y motive h₁$ h-1 h-2
  = Or:casesOn
    {Not (#130 y)}
    {Not (#31 y x)}
    {λ (x# : Or (Not (#130 y)) (Not (#31 y x))) → motive x#}
    h₁$
    (λ (h$ : Not (#130 y)) → h-1 h$)
    (λ (h$ : Not (#31 y x)) → h-2 h$)

--theorem
Nat:mod-lt : (x : Nat) → {y : Nat} → #150 y #4 → #26 (#19 x y) y
Nat:mod-lt x {y}
  = Nat:mod:inductionOn#z
    {λ (x# : Nat) → λ (y# : Nat) → #150 y# #4 → #26 (#19 x# y#) y#}
    x
    y
    (λ (x# : Nat) →
      λ (y# : Nat) →
        λ (h : And (#130 y#) (#31 y# x#)) →
          λ (h₂ : #150 y# #4 → #26 (#19 (#136 x# y#) y#) y#) →
            λ (h₃ : #150 y# #4) →
              Nat:div-rec-lemma:match-1
                {x#}
                {y#}
                (λ (_ : And (#130 y#) (#31 y# x#)) → #26 (#19 x# y#) y#)
                h
                (λ (_ : #130 y#) →
                  λ (h₁ : #31 y# x#) →
                    Eq:mpr#z
                      {#26 (#19 x# y#) y#}
                      {#26 (#19 (#136 x# y#) y#) y#}
                      (id#z
                        {#11 (#26 (#19 x# y#) y#) (#26 (#19 (#136 x# y#) y#) y#)}
                        (#13 {#19 x# y#} {#19 (#136 x# y#) y#} (λ (-a : Nat) → #26 -a y#) (Nat:mod-eq-sub-mod {x#} {y#} h₁)))
                      (h₂ h₃)))
    (λ (x# : Nat) →
      λ (y# : Nat) →
        λ (h₁ : Not (And (#130 y#) (#31 y# x#))) →
          λ (h₂ : #150 y# #4) →
            letFun#zz
              {Or (Not (#130 y#)) (Not (#31 y# x#))}
              {λ (_ : Or (Not (#130 y#)) (Not (#31 y# x#))) → #26 (#19 x# y#) y#}
              (Iff:mp
                {Not (And (#130 y#) (#31 y# x#))}
                {Or (Not (#130 y#)) (Not (#31 y# x#))}
                (Decidable:not-and-iff-or-not (#130 y#) (#31 y# x#) {{Nat:decLt #4 y#}} {{Nat:decLe y# x#}})
                h₁)
              (λ (h₁# : Or (Not (#130 y#)) (Not (#31 y# x#))) →
                Nat:mod-lt:match-1
                  x#
                  y#
                  (λ (_ : Or (Not (#130 y#)) (Not (#31 y# x#))) → #26 (#19 x# y#) y#)
                  h₁#
                  (λ (h₁#1 : Not (#130 y#)) → absurd#z {#150 y# #4} {#26 (#19 x# y#) y#} h₂ h₁#1)
                  (λ (h₁#1 : Not (#31 y# x#)) →
                    letFun#zz
                      {#150 y# x#}
                      {λ (_ : #150 y# x#) → #26 (#19 x# y#) y#}
                      (Nat:gt-of-not-le {y#} {x#} h₁#1)
                      (λ (hgt : #150 y# x#) →
                        letFun#zz
                          {#0 (#19 x# y#) x#}
                          {λ (_ : #0 (#19 x# y#) x#) → #26 (#19 x# y#) y#}
                          (Nat:mod-eq-of-lt {x#} {y#} hgt)
                          (λ (heq : #0 (#19 x# y#) x#) →
                            Eq:mp#z
                              {#150 y# x#}
                              {#150 y# (#19 x# y#)}
                              (#13 {x#} {#19 x# y#} (λ (-a : Nat) → #150 y# -a) (#15 {#19 x# y#} {x#} heq))
                              hgt)))))

--def
Ne#n : {u : Level} → {α : Set u} → α → α → Prop
Ne#n {u} {α} a b = Not (Eq#n {u} {α} a b)

--def
#179 : Nat → Nat → Prop
#179 = Ne#n {lone} {Nat}

--def
#180 : Set₁
#180 = (a$ : Nat) → #179 a$ #4 → Prop

--def
#181 : Prop
#181 = #179 #4 #4

--def
Nat:zero-lt-of-ne-zero:match-1 :
  (motive : #180) →
    (a$ : Nat) →
      (h : #179 a$ #4) → ((h# : #181) → motive #4 h#) → ((a : Nat) → (h# : #179 (#16 a #17) #4) → motive (Nat:succ a) h#) → motive a$ h
Nat:zero-lt-of-ne-zero:match-1 motive a$ h h-1 h-2
  = Nat:casesOn#z
    {λ (x : Nat) → (h# : #179 x #4) → motive x h#}
    a$
    (λ (h# : #179 Nat:zero #4) → h-1 h#)
    (λ (n$ : Nat) → λ (h# : #179 (Nat:succ n$) #4) → h-2 n$ h#)
    h

--theorem
Nat:zero-lt-of-ne-zero : {a : Nat} → #179 a #4 → #130 a
Nat:zero-lt-of-ne-zero {a} h
  = Nat:zero-lt-of-ne-zero:match-1
    (λ (a$ : Nat) → λ (_ : #179 a$ #4) → #130 a$)
    a
    h
    (λ (h# : #179 #4 #4) → absurd#z {#69 #4} {#137} (#62 #4) h#)
    (λ (a# : Nat) → λ (_ : #179 (#16 a# #17) #4) → Nat:zero-lt-succ a#)

--theorem
Nat:gcd:-unary:proof-2 : (m : #7) → (n : #7) → Not (#25 m #4) → #24 (#22 (#149 n m) m) (#22 m n)
Nat:gcd:-unary:proof-2 m n h$
  = id#z
    {#24 (#22 (#149 n m) m) (#22 m n)}
    (Eq:mpr#z
      {#26 (#149 n m) m}
      {#26 (#149 n m) m}
      (id#z {#11 (#26 (#149 n m) m) (#26 (#149 n m) m)} (Init:Core:-auxLemma:7 {lzero} {Nat} {{instLTNat}} {m} {#149 n m}))
      (Nat:mod-lt n {m} (Nat:zero-lt-of-ne-zero {m} h$)))

--def
Nat:gcd:-unary : #21 → Nat
Nat:gcd:-unary
  = WellFounded:fix#nn {lone} {lone}
    {#21}
    {λ (_ : #21) → Nat}
    {#24}
    Nat:gcd:-unary:proof-1
    (λ (x : #21) →
      λ (a$ : (y : #21) → #24 y x → Nat) →
        #23
          {λ (-x : #21) → ((y : #21) → #24 y -x → Nat) → Nat}
          x
          (λ (m : #7) →
            λ (n : #7) →
              λ (a$1 : (y : #21) → #24 y (#22 m n) → Nat) →
                dite#n {lone}
                  {Nat}
                  (#25 m #4)
                  {{instDecidableEqNat m #4}}
                  (λ (_ : #25 m #4) → n)
                  (λ (h$ : Not (#25 m #4)) →
                    a$1
                      (#22 (HMod:hMod {lzero} {lzero} {lzero} {#7} {#7} {#7} {{instHMod {lzero} {#7} {{Nat:instMod}}}} n m) m)
                      (Nat:gcd:-unary:proof-2 m n h$)))
          a$)

--def
Nat:gcd : #7 → #7 → Nat
Nat:gcd m n = Nat:gcd:-unary (PSigma:mk#nn {lone} {lone} {#7} {λ (_ : #7) → #7} m n)

--def
#6 : Nat → Prop
#6 n = #0 (Nat:gcd n n) n

--def
#8 : #7 → Nat
#8 = Nat:gcd #4

--def
#9 : Nat
#9 = #8 (OfNat:ofNat {lzero} {#7} 0 {{#3}})

--def
#10 : Prop
#10 = #0 #9 #4

--def
#12 : {a : Prop} → {b : Prop} → {c : Prop} → #11 a b → #11 b c → #11 a c
#12 {a} {b} {c} = Eq:trans#n {lone} {Prop} {a} {b} {c}

--record 0 0->0 0 0
record True : Prop where
  constructor True:intro

--theorem
trivial : True
trivial = True:intro

--theorem
eq-true : {p : Prop} → p → #11 p True
eq-true {p} h = propext {p} {True} (Iff:intro {p} {True} (λ (_ : p) → trivial) (λ (_ : True) → h))

--theorem
eq-self#n : {u-1 : Level} → {α : Set u-1} → (a : α) → #11 (Eq#n {u-1} {α} a a) True
eq-self#n {u-1} {α} a = eq-true {Eq#n {u-1} {α} a a} (rfl#n {u-1} {α} {a})

--def
#14 : (a : Nat) → #11 (#0 a a) True
#14 = eq-self#n {lone} {Nat}

--theorem
of-eq-true : {p : Prop} → #11 p True → p
of-eq-true {p} h
  = Eq:rec#zn {lone}
    {Prop}
    {True}
    {λ (x$ : Prop) → λ (_ : #11 True x$) → x$}
    trivial
    {p}
    (Eq:symm#n {lone} {Prop} {p} {True} h)

--def
#182#z : Set₁
#182#z = Nat → Prop

--def
Nat:casesAuxOn#z : {motive : #182#z} → (t : Nat) → motive #4 → ((n : Nat) → motive (#16 n #17)) → motive t
Nat:casesAuxOn#z {motive} t zero succ = Nat:casesOn#z {λ (x$ : Nat) → motive x$} t zero succ

--def
#183 : #21 → Set₁
#183 _ = Nat

--def
#184 : (t : #21) → ((fst : #7) → (snd : #7) → ((y : #21) → #24 y (#22 fst snd) → Nat) → Nat) → ((y : #21) → #24 y t → Nat) → Nat
#184 = #23 {λ (-x : #21) → ((y : #21) → #24 y -x → Nat) → Nat}

--def
#185 : (m : #7) → (n : #7) → ((y : #21) → #24 y (#22 m n) → Nat) → Nat
#185 m n a$
  = dite#n {lone}
    {Nat}
    (#25 m #4)
    {{instDecidableEqNat m #4}}
    (λ (_ : #25 m #4) → n)
    (λ (h$ : Not (#25 m #4)) → a$ (#22 (#149 n m) m) (Nat:gcd:-unary:proof-2 m n h$))

--def
#186 : (x : #21) → ((y : #21) → #24 y x → Nat) → Nat
#186 x a$ = #184 x #185 a$

--def
#187 : #21 → Nat
#187 = WellFounded:fix#nn {lone} {lone} {#21} {#183} {#24} Nat:gcd:-unary:proof-1 #186

--theorem
Nat:gcd:eq-1 : (m : Nat) → (n : Nat) → #0 (Nat:gcd m n) (#152 (#25 m #4) {{instDecidableEqNat m #4}} n (Nat:gcd (#149 n m) m))
Nat:gcd:eq-1 m n
  = id#z
    {#0 (Nat:gcd m n) (#152 (#25 m #4) {{instDecidableEqNat m #4}} n (Nat:gcd (#149 n m) m))}
    (id#z
      {#0 (Nat:gcd:-unary (#22 m n)) (#152 (#25 m #4) {{instDecidableEqNat m #4}} n (Nat:gcd (#149 n m) m))}
      (#18
        {#187 (#22 m n)}
        {#184 (#22 m n) #185 (λ (y : #21) → λ (_ : #24 y (#22 m n)) → #187 y)}
        {#152 (#25 m #4) {{instDecidableEqNat m #4}} n (Nat:gcd (#149 n m) m)}
        (WellFounded:fix-eq#nn {lone} {lone} {#21} {#183} {#24} Nat:gcd:-unary:proof-1 #186 (#22 m n))
        (#62 (#184 (#22 m n) #185 (λ (y : #21) → λ (_ : #24 y (#22 m n)) → #187 y)))))

--theorem
Nat:gcd-succ : (x : Nat) → (y : Nat) → #0 (Nat:gcd (Nat:succ x) y) (Nat:gcd (#19 y (Nat:succ x)) (Nat:succ x))
Nat:gcd-succ x y
  = Eq:mpr#z
    {#0 (Nat:gcd (Nat:succ x) y) (Nat:gcd (#19 y (Nat:succ x)) (Nat:succ x))}
    {#0
      (#152 (#25 (Nat:succ x) #4) {{instDecidableEqNat (Nat:succ x) #4}} y (Nat:gcd (#149 y (Nat:succ x)) (Nat:succ x)))
      (Nat:gcd (#19 y (Nat:succ x)) (Nat:succ x))}
    (id#z
      {#11
        (#0 (Nat:gcd (Nat:succ x) y) (Nat:gcd (#19 y (Nat:succ x)) (Nat:succ x)))
        (#0
          (#152 (#25 (Nat:succ x) #4) {{instDecidableEqNat (Nat:succ x) #4}} y (Nat:gcd (#149 y (Nat:succ x)) (Nat:succ x)))
          (Nat:gcd (#19 y (Nat:succ x)) (Nat:succ x)))}
      (#13
        {Nat:gcd (Nat:succ x) y}
        {#152 (#25 (Nat:succ x) #4) {{instDecidableEqNat (Nat:succ x) #4}} y (Nat:gcd (#149 y (Nat:succ x)) (Nat:succ x))}
        (λ (-a : Nat) → #0 -a (Nat:gcd (#19 y (Nat:succ x)) (Nat:succ x)))
        (Nat:gcd:eq-1 (Nat:succ x) y)))
    (#62 (#152 (#25 (Nat:succ x) #4) {{instDecidableEqNat (Nat:succ x) #4}} y (Nat:gcd (#149 y (Nat:succ x)) (Nat:succ x))))

--def
#188 : #7
#188 = OfNat:ofNat {lzero} {#7} 0 {{#3}}

--def
#189 : #7 → Nat
#189 = Nat:gcd #188

--def
#190 : Nat → Nat → Nat
#190 = #152 (#25 #188 #4) {{instDecidableEqNat #188 #4}}

--theorem
Nat:gcd-zero-left : (y : Nat) → #0 (#189 y) y
Nat:gcd-zero-left y
  = Eq:mpr#z
    {#0 (#189 y) y}
    {#0 (#190 y (Nat:gcd (#149 y #188) #188)) y}
    (id#z
      {#11 (#0 (#189 y) y) (#0 (#190 y (Nat:gcd (#149 y #188) #188)) y)}
      (#13 {#189 y} {#190 y (Nat:gcd (#149 y #188) #188)} (λ (-a : Nat) → #0 -a y) (Nat:gcd:eq-1 #188 y)))
    (#62 (#190 y (Nat:gcd (#149 y #188) #188)))

--def
#191 : Nat → Prop
#191 n = #0 (Nat:gcd n #188) n

--def
#192 : Nat
#192 = #189 #188

--def
#193 : Prop
#193 = #0 #192 #4

--def
#194 : Nat → Nat
#194 = #19 #188

--theorem
Nat:gcd-zero-right : (n : Nat) → #0 (Nat:gcd n #188) n
Nat:gcd-zero-right n
  = Nat:casesAuxOn#z
    {λ (a$ : Nat) → #0 n a$ → #0 (Nat:gcd n #188) n}
    n
    (λ (h$ : #0 n #4) →
      #5
        {#4}
        {#191}
        (of-eq-true
          {#193}
          (#12 {#193} {#0 #188 #4} {True} (#13 {#192} {#188} (λ (x : Nat) → #0 x #4) (Nat:gcd-zero-left #188)) (#14 #188)))
        {n}
        (#15 {n} {#4} h$))
    (λ (n# : Nat) →
      λ (h$ : #0 n (#16 n# #17)) →
        #5
          {#16 n# #17}
          {#191}
          (Eq:mpr#z
            {#0 (Nat:gcd (#16 n# #17) #188) (#16 n# #17)}
            {#0 (Nat:gcd (#194 (Nat:succ n#)) (Nat:succ n#)) (#16 n# #17)}
            (id#z
              {#11 (#0 (Nat:gcd (#16 n# #17) #188) (#16 n# #17)) (#0 (Nat:gcd (#194 (Nat:succ n#)) (Nat:succ n#)) (#16 n# #17))}
              (#13
                {Nat:gcd (Nat:succ n#) #188}
                {Nat:gcd (#194 (Nat:succ n#)) (Nat:succ n#)}
                (λ (-a : Nat) → #0 -a (#16 n# #17))
                (Nat:gcd-succ n# #188)))
            (Nat:gcd-zero-left (Nat:succ n#)))
          {n}
          (#15 {n} {#16 n# #17} h$))
    (#62 n)

--def
#195 : Nat → Prop
#195 -a = #0 -a #4

--def
#196 : Set₁
#196 = Nat → Nat

--def
#197 : #196
#197 = #19 #4

--def
#198 : Prop
#198 = #69 #4

--def
#199 : Nat → Prop
#199 x$ = #0 (#136 x$ x$) #4

--def
#200 : Nat → Set₁
#200 = Nat:below#z {#199}

--def
#201 : Nat
#201 = #136 #4 #4

--def
#202 : Prop
#202 = #0 #201 #4

--def
#203 : #198
#203 = #62 #4

--theorem
Nat:succ-sub-succ : (n : Nat) → (m : Nat) → #0 (#136 (Nat:succ n) (Nat:succ m)) (#136 n m)
Nat:succ-sub-succ n m = Nat:succ-sub-succ-eq-sub n m

--theorem
Nat:sub-self : (n : Nat) → #0 (#136 n n) #4
Nat:sub-self x$
  = Nat:brecOn#z
    {#199}
    x$
    (λ (x$1 : Nat) →
      λ (f : #200 x$1) →
        Nat:zero-add:match-1
          (λ (x$2 : Nat) → #200 x$2 → #0 (#136 x$2 x$2) #4)
          x$1
          (λ (_ : Unit) →
            λ (_ : #200 #4) → Eq:mpr#z {#202} {#198} (id#z {#11 #202 #198} (#13 {#201} {#4} #195 (Nat:sub-zero #4))) #203)
          (λ (n : Nat) →
            λ (x$2 : #200 (Nat:succ n)) →
              Eq:mpr#z
                {#0 (#136 (Nat:succ n) (Nat:succ n)) #4}
                {#0 (#136 n n) #4}
                (id#z
                  {#11 (#0 (#136 (Nat:succ n) (Nat:succ n)) #4) (#0 (#136 n n) #4)}
                  (#13 {#136 (Nat:succ n) (Nat:succ n)} {#136 n n} #195 (Nat:succ-sub-succ n n)))
                (Eq:mpr#z
                  {#0 (#136 n n) #4}
                  {#198}
                  (id#z {#11 (#0 (#136 n n) #4) #198} (#13 {#136 n n} {#4} #195 (PProd#zn.fst {lone} x$2)))
                  #203))
          f)

--def
#204 : Nat → Nat
#204 = #136 #4

--def
#205 : Prop
#205 = False

--def
False:elim#z : {C : Prop} → False → C
False:elim#z {C} h = False:rec#z (λ (_ : False) → C) h

--theorem
eq-false : {p : Prop} → Not p → #11 p False
eq-false {p} h
  = propext
    {p}
    {False}
    (Iff:intro {p} {False} (λ (h' : p) → absurd#z {p} {False} h' h) (λ (h' : False) → False:elim#z {p} h'))

--theorem
Init:Data:Nat:Basic:-auxLemma:7 : (n : Nat) → #11 (#26 n n) False
Init:Data:Nat:Basic:-auxLemma:7 n = eq-false {#26 n n} (Nat:lt-irrefl n)

--theorem
not-false : Not False
not-false = id#z {False}

--def
instDecidableFalse : Decidable False
instDecidableFalse = Decidable:isFalse {False} not-false

--def
#206 : {a : Prop} → {motive : Prop → Prop} → motive a → {b : Prop} → #11 a b → motive b
#206 {a} {motive} = Eq:ndrec#zn {lone} {Prop} {a} {motive}

--def
#207 : {a : Prop} → {b : Prop} → #11 a b → #11 b a
#207 {a} {b} = Eq:symm#n {lone} {Prop} {a} {b}

--def
Decidable:byCases#z : {p : Prop} → {q : Prop} → {{Decidable p}} → (p → q) → (Not p → q) → q
Decidable:byCases#z {p} {q} {{dec}} h1 h2
  = Decidable:byCases:match-1#z {p} (λ (_ : Decidable p) → q) dec (λ (h : p) → h1 h) (λ (h : Not p) → h2 h)

--theorem
Decidable:em : (p : Prop) → {{Decidable p}} → Or p (Not p)
Decidable:em p {{inst$}} = Decidable:byCases#z {p} {Or p (Not p)} {{inst$}} (Or:inl {p} {Not p}) (Or:inr {p} {Not p})

--theorem
ite-congr#n :
  {u-1 : Level} →
    {α : Set u-1} →
      {b : Prop} →
        {c : Prop} →
          {x : α} →
            {y : α} →
              {u : α} →
                {v : α} →
                  {s : Decidable b} →
                    {{inst$ : Decidable c}} →
                      #11 b c →
                        (c → Eq#n {u-1} {α} x u) →
                          (Not c → Eq#n {u-1} {α} y v) →
                            Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) (ite#n {u-1} {α} c {{inst$}} u v)
ite-congr#n {u-1} {α} {b} {c} {x} {y} {u} {v} {s} {{inst$}} h₁ h₂ h₃
  = Or:casesOn
    {c}
    {Not c}
    {λ (t$ : Or c (Not c)) →
      Eq#z {Or c (Not c)} (Decidable:em c {{inst$}}) t$ →
        Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) (ite#n {u-1} {α} c {{inst$}} u v)}
    (Decidable:em c {{inst$}})
    (λ (h : c) →
      λ (_ : Eq#z {Or c (Not c)} (Decidable:em c {{inst$}}) (Or:inl {c} {Not c} h)) →
        Eq:mpr#z
          {Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) (ite#n {u-1} {α} c {{inst$}} u v)}
          {Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) u}
          (id#z
            {#11
              (Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) (ite#n {u-1} {α} c {{inst$}} u v))
              (Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) u)}
            (congrArg#nn {u-1} {lone}
              {α}
              {Prop}
              {ite#n {u-1} {α} c {{inst$}} u v}
              {u}
              (λ (-a : α) → Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) -a)
              (if-pos#n {u-1} {c} {inst$} h {α} {u} {v})))
          (#206
            {c}
            {λ (b# : Prop) → {s# : Decidable b#} → Eq#n {u-1} {α} (ite#n {u-1} {α} b# {{s#}} x y) u}
            (λ {s# : Decidable c} →
              Eq:mpr#z
                {Eq#n {u-1} {α} (ite#n {u-1} {α} c {{s#}} x y) u}
                {Eq#n {u-1} {α} x u}
                (id#z
                  {#11 (Eq#n {u-1} {α} (ite#n {u-1} {α} c {{s#}} x y) u) (Eq#n {u-1} {α} x u)}
                  (congrArg#nn {u-1} {lone}
                    {α}
                    {Prop}
                    {ite#n {u-1} {α} c {{s#}} x y}
                    {x}
                    (λ (-a : α) → Eq#n {u-1} {α} -a u)
                    (if-pos#n {u-1} {c} {s#} h {α} {x} {y})))
                (h₂ h))
            {b}
            (#207 {b} {c} h₁)
            {s}))
    (λ (h : Not c) →
      λ (_ : Eq#z {Or c (Not c)} (Decidable:em c {{inst$}}) (Or:inr {c} {Not c} h)) →
        Eq:mpr#z
          {Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) (ite#n {u-1} {α} c {{inst$}} u v)}
          {Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) v}
          (id#z
            {#11
              (Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) (ite#n {u-1} {α} c {{inst$}} u v))
              (Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) v)}
            (congrArg#nn {u-1} {lone}
              {α}
              {Prop}
              {ite#n {u-1} {α} c {{inst$}} u v}
              {v}
              (λ (-a : α) → Eq#n {u-1} {α} (ite#n {u-1} {α} b {{s}} x y) -a)
              (if-neg#n {u-1} {c} {inst$} h {α} {u} {v})))
          (#206
            {c}
            {λ (b# : Prop) → {s# : Decidable b#} → Eq#n {u-1} {α} (ite#n {u-1} {α} b# {{s#}} x y) v}
            (λ {s# : Decidable c} →
              Eq:mpr#z
                {Eq#n {u-1} {α} (ite#n {u-1} {α} c {{s#}} x y) v}
                {Eq#n {u-1} {α} y v}
                (id#z
                  {#11 (Eq#n {u-1} {α} (ite#n {u-1} {α} c {{s#}} x y) v) (Eq#n {u-1} {α} y v)}
                  (congrArg#nn {u-1} {lone}
                    {α}
                    {Prop}
                    {ite#n {u-1} {α} c {{s#}} x y}
                    {y}
                    (λ (-a : α) → Eq#n {u-1} {α} -a v)
                    (if-neg#n {u-1} {c} {s#} h {α} {x} {y})))
                (h₃ h))
            {b}
            (#207 {b} {c} h₁)
            {s}))
    (Eq:refl#z {Or c (Not c)} (Decidable:em c {{inst$}}))

--theorem
ite-cond-eq-false#n :
  {u : Level} →
    {α : Set u} → {c : Prop} → {x$ : Decidable c} → (a : α) → (b : α) → #11 c False → Eq#n {u} {α} (ite#n {u} {α} c {{x$}} a b) b
ite-cond-eq-false#n {u} {α} {c} {x$} a b h
  = of-eq-true
    {Eq#n {u} {α} (ite#n {u} {α} c {{x$}} a b) b}
    (#12
      {Eq#n {u} {α} (ite#n {u} {α} c {{x$}} a b) b}
      {Eq#n {u} {α} (ite#n {u} {α} False {{instDecidableFalse}} a b) b}
      {True}
      (congrArg#nn {u} {lone}
        {α}
        {Prop}
        {ite#n {u} {α} c {{x$}} a b}
        {ite#n {u} {α} False {{instDecidableFalse}} a b}
        (λ (x : α) → Eq#n {u} {α} x b)
        (ite-congr#n {u}
          {α}
          {c}
          {False}
          {a}
          {b}
          {a}
          {b}
          {x$}
          {{instDecidableFalse}}
          h
          (λ (_ : False) → Eq:refl#n {u} {α} a)
          (λ (_ : Not False) → Eq:refl#n {u} {α} b)))
      (eq-self#n {u} {α} b))

--def
#208 : Prop
#208 = #72 #4

--def
Decidable:decide : (p : Prop) → {{Decidable p}} → Bool
Decidable:decide p {{h}}
  = Decidable:casesOn#n {lone} {p} {λ (_ : Decidable p) → Bool} h (λ (_ : Not p) → Bool:false) (λ (_ : p) → Bool:true)

--def
decide-eq-false:match-1 :
  {p : Prop} →
    (motive : Decidable p → Not p → Prop) →
      (x$ : Decidable p) →
        (x$1 : Not p) →
          ((h₁ : p) → (h₂ : Not p) → motive (Decidable:isTrue {p} h₁) h₂) →
            ((h$ : Not p) → (x$2 : Not p) → motive (Decidable:isFalse {p} h$) x$2) → motive x$ x$1
decide-eq-false:match-1 {p} motive x$ x$1 h-1 h-2
  = Decidable:casesOn#z {p} {λ (x : Decidable p) → motive x x$1} x$ (λ (h$ : Not p) → h-2 h$ x$1) (λ (h$ : p) → h-1 h$ x$1)

--theorem
decide-eq-false : {p : Prop} → {{inst$ : Decidable p}} → Not p → #78 (Decidable:decide p {{inst$}}) Bool:false
decide-eq-false {p} {{x$}} x$1
  = decide-eq-false:match-1
    {p}
    (λ (x$2 : Decidable p) → λ (_ : Not p) → #78 (Decidable:decide p {{x$2}}) Bool:false)
    x$
    x$1
    (λ (h₁ : p) → λ (h₂ : Not p) → absurd#z {p} {#78 (Decidable:decide p {{Decidable:isTrue {p} h₁}}) Bool:false} h₁ h₂)
    (λ (h$ : Not p) → λ (_ : Not p) → #102 {Decidable:decide p {{Decidable:isFalse {p} h$}}})

--def
#209 : Set₁
#209 = (x$ : Bool) → #78 x$ Bool:false → Prop

--def
#210 : Prop
#210 = #101 Bool:false

--def
ne-true-of-eq-false:match-1 :
  (motive : #209) →
    (x$ : Bool) → (x$1 : #78 x$ Bool:false) → ((h : #106) → motive Bool:true h) → ((x$2 : #210) → motive Bool:false x$2) → motive x$ x$1
ne-true-of-eq-false:match-1 motive x$ x$1 h-1 h-2
  = Bool:casesOn#z {λ (x : Bool) → (x$2 : #78 x Bool:false) → motive x x$2} x$ (λ (x$2 : #210) → h-2 x$2) (λ (x$2 : #106) → h-1 x$2) x$1

--theorem
ne-true-of-eq-false : {b : Bool} → #78 b Bool:false → Not (#78 b Bool:true)
ne-true-of-eq-false {x$} x$1
  = ne-true-of-eq-false:match-1
    (λ (x$2 : Bool) → λ (_ : #78 x$2 Bool:false) → Not (#78 x$2 Bool:true))
    x$
    x$1
    (λ (h : #106) → Bool:noConfusion#z {Not (#105 Bool:true)} {Bool:true} {Bool:false} h)
    (λ (_ : #101 Bool:false) → λ (h : #103) → #104 {Bool:false} {Bool:true} h)

--def
of-decide-eq-true:match-1 :
  {p : Prop} →
    (motive : Decidable p → Prop) →
      (inst$ : Decidable p) →
        ((h₁ : p) → motive (Decidable:isTrue {p} h₁)) → ((h₁ : Not p) → motive (Decidable:isFalse {p} h₁)) → motive inst$
of-decide-eq-true:match-1 {p} motive inst$ h-1 h-2
  = Decidable:casesOn#z {p} {λ (x : Decidable p) → motive x} inst$ (λ (h$ : Not p) → h-2 h$) (λ (h$ : p) → h-1 h$)

--theorem
of-decide-eq-true : {p : Prop} → {{inst : Decidable p}} → #78 (Decidable:decide p {{inst}}) Bool:true → p
of-decide-eq-true {p} {{inst}} h
  = of-decide-eq-true:match-1
    {p}
    (λ (_ : Decidable p) → p)
    inst
    (λ (h₁ : p) → h₁)
    (λ (h₁ : Not p) →
      absurd#z
        {#78 (Decidable:decide p {{inst}}) Bool:true}
        {p}
        h
        (ne-true-of-eq-false {Decidable:decide p {{inst}}} (decide-eq-false {p} {{inst}} h₁)))

--theorem
Nat:le-zero-eq : (a : Nat) → #11 (#31 a #4) (#0 a #4)
Nat:le-zero-eq a
  = propext
    {#31 a #4}
    {#0 a #4}
    (Iff:intro
      {#31 a #4}
      {#0 a #4}
      (λ (h : #31 a #4) → Nat:le-antisymm {a} {#4} h (Nat:zero-le a))
      (λ (h : #0 a #4) →
        Eq:mpr#z
          {#31 a #4}
          {#208}
          (id#z {#11 (#31 a #4) #208} (#13 {a} {#4} (λ (-a : Nat) → #31 -a #4) h))
          (of-decide-eq-true {#208} {{Nat:decLe #4 #4}} (#116 Bool:true))))

--def
Nat:zero-mod:match-1 :
  (b : Nat) →
    (motive : And (#130 b) (#0 b #4) → Prop) →
      (h$ : And (#130 b) (#0 b #4)) → ((h₁ : #130 b) → (h₂ : #0 b #4) → motive (And:intro {#130 b} {#0 b #4} h₁ h₂)) → motive h$
Nat:zero-mod:match-1 b motive h$ h-1
  = And:casesOn#z
    {#130 b}
    {#0 b #4}
    {λ (x : And (#130 b) (#0 b #4)) → motive x}
    h$
    (λ (left$ : #130 b) → λ (right$ : #0 b #4) → h-1 left$ right$)

--theorem
Nat:zero-mod : (b : Nat) → #0 (#197 b) #4
Nat:zero-mod b
  = Eq:mpr#z
    {#0 (#197 b) #4}
    {#0
      (#152 (And (#130 b) (#31 b #4)) {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}} (#19 (#204 b) b) #4)
      #4}
    (id#z
      {#11
        (#0 (#197 b) #4)
        (#0
          (#152
            (And (#130 b) (#31 b #4))
            {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}}
            (#19 (#204 b) b)
            #4)
          #4)}
      (#13
        {#197 b}
        {#152 (And (#130 b) (#31 b #4)) {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}} (#19 (#204 b) b) #4}
        #195
        (Nat:mod-eq #4 b)))
    (letFun#zz
      {Not (And (#130 b) (#0 b #4))}
      {λ (_ : Not (And (#130 b) (#0 b #4))) →
        #0
          (#152
            (And (#130 b) (#31 b #4))
            {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}}
            (#19 (#204 b) b)
            #4)
          #4}
      (λ (h$ : And (#130 b) (#0 b #4)) →
        Nat:zero-mod:match-1
          b
          (λ (_ : And (#130 b) (#0 b #4)) → #205)
          h$
          (λ (h₁ : #130 b) →
            λ (h₂ : #0 b #4) →
              False:elim#z
                {#205}
                (Eq:mp#z
                  {#130 b}
                  {False}
                  (#12 {#130 b} {#137} {False} (#13 {b} {#4} #130 h₂) (Init:Data:Nat:Basic:-auxLemma:7 #4))
                  h₁)))
      (λ (this : Not (And (#130 b) (#0 b #4))) →
        of-eq-true
          {#0
            (#152
              (And (#130 b) (#31 b #4))
              {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}}
              (#19 (#204 b) b)
              #4)
            #4}
          (#12
            {#0
              (#152
                (And (#130 b) (#31 b #4))
                {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}}
                (#19 (#204 b) b)
                #4)
              #4}
            {#198}
            {True}
            (#13
              {#152
                (And (#130 b) (#31 b #4))
                {{instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}}
                (#19 (#204 b) b)
                #4}
              {#4}
              (λ (x : Nat) → #0 x #4)
              (ite-cond-eq-false#n {lone}
                {Nat}
                {And (#130 b) (#31 b #4)}
                {instDecidableAnd {#130 b} {#31 b #4} {{#153 b}} {{Nat:decLe b #4}}}
                (#19 (#204 b) b)
                #4
                (#12
                  {And (#130 b) (#31 b #4)}
                  {And (#130 b) (#0 b #4)}
                  {False}
                  (congrArg#nn {lone} {lone} {Prop} {Prop} {#31 b #4} {#0 b #4} (And (#130 b)) (Nat:le-zero-eq b))
                  (eq-false {And (#130 b) (#0 b #4)} this))))
            (#14 #4))))

--theorem
Nat:mod-self : (n : Nat) → #0 (#19 n n) #4
Nat:mod-self n
  = Eq:mpr#z
    {#0 (#19 n n) #4}
    {#0 (#19 (#136 n n) n) #4}
    (id#z
      {#11 (#0 (#19 n n) #4) (#0 (#19 (#136 n n) n) #4)}
      (#13 {#19 n n} {#19 (#136 n n) n} #195 (Nat:mod-eq-sub-mod {n} {n} (Nat:le-refl n))))
    (Eq:mpr#z
      {#0 (#19 (#136 n n) n) #4}
      {#0 (#197 n) #4}
      (id#z
        {#11 (#0 (#19 (#136 n n) n) #4) (#0 (#197 n) #4)}
        (#13 {#136 n n} {#4} (λ (-a : Nat) → #0 (#19 -a n) #4) (Nat:sub-self n)))
      (Eq:mpr#z {#0 (#197 n) #4} {#198} (id#z {#11 (#0 (#197 n) #4) #198} (#13 {#197 n} {#4} #195 (Nat:zero-mod n))) (#62 #4)))

--theorem
Nat:gcd-self : (n : Nat) → #0 (Nat:gcd n n) n
Nat:gcd-self n
  = Nat:casesAuxOn#z
    {λ (a$ : Nat) → #0 n a$ → #0 (Nat:gcd n n) n}
    n
    (λ (h$ : #0 n #4) →
      #5
        {#4}
        {#6}
        (of-eq-true
          {#10}
          (#12 {#10} {#0 #4 #4} {True} (#13 {#9} {#4} (λ (x : Nat) → #0 x #4) (Nat:gcd-zero-right #4)) (#14 #4)))
        {n}
        (#15 {n} {#4} h$))
    (λ (n$ : Nat) →
      λ (h$ : #0 n (#16 n$ #17)) →
        #5
          {#16 n$ #17}
          {#6}
          (of-eq-true
            {#0 (Nat:gcd (Nat:succ n$) (#16 n$ #17)) (#16 n$ #17)}
            (#12
              {#0 (Nat:gcd (Nat:succ n$) (#16 n$ #17)) (#16 n$ #17)}
              {#0 (#16 n$ #17) (#16 n$ #17)}
              {True}
              (#13
                {Nat:gcd (Nat:succ n$) (#16 n$ #17)}
                {#16 n$ #17}
                (λ (x : Nat) → #0 x (#16 n$ #17))
                (#18
                  {Nat:gcd (Nat:succ n$) (#16 n$ #17)}
                  {Nat:gcd (#19 (#16 n$ #17) (Nat:succ n$)) (Nat:succ n$)}
                  {#16 n$ #17}
                  (Nat:gcd-succ n$ (#16 n$ #17))
                  (#18
                    {Nat:gcd (#19 (#16 n$ #17) (#16 n$ #17)) (#16 n$ #17)}
                    {#8 (#16 n$ #17)}
                    {#16 n$ #17}
                    (congrArg#nn {lone} {lone}
                      {#7}
                      {Nat}
                      {#19 (#16 n$ #17) (#16 n$ #17)}
                      {#4}
                      (λ (x : #7) → Nat:gcd x (#16 n$ #17))
                      (Nat:mod-self (#16 n$ #17)))
                    (Nat:gcd-zero-left (#16 n$ #17)))))
              (#14 (#16 n$ #17))))
          {n}
          (#15 {n} {#16 n$ #17} h$))
    (Eq:refl#n {lone} {Nat} n)
