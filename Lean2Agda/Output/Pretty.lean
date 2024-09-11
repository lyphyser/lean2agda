import Lean.Data.Format

open Std
open Std.Format
open MonadPrettyFormat

private structure SpaceResult where
  foundLine              : Bool := false
  foundFlattenedHardLine : Bool := false
  space                  : Nat  := 0
  deriving Inhabited

@[inline] private def merge (w : Nat) (r₁ : SpaceResult) (r₂ : Nat → SpaceResult) : SpaceResult :=
  if r₁.space > w || r₁.foundLine then
    r₁
  else
    let r₂ := r₂ (w - r₁.space);
    { r₂ with space := r₁.space + r₂.space }

private def spaceUptoLine : Format → (Bool × Bool) → Int → Nat → SpaceResult
  | nil,          _,       _, _ => {}
  | line,         flatten, _, _ => if flatten.fst then { space := 1 } else { foundLine := true }
  | align force,  flatten, m, w =>
    if flatten.fst && !force then {}
    else if w < m then
      { space := (m - w).toNat }
    else
      { foundLine := true }
  | text s,       flatten, _, _ =>
    let p := s.posOf '\n'
    let off := s.offsetOfPos p
    { foundLine := p != s.endPos, foundFlattenedHardLine := flatten.fst && p != s.endPos, space := off }
  | append f₁ f₂, flatten, m, w => merge w (spaceUptoLine f₁ flatten m w) (spaceUptoLine f₂ flatten m)
  | nest n f,     flatten, m, w => spaceUptoLine f flatten (m - n) w
  | group f _,    flatten, m, w => spaceUptoLine f (flatten.snd, flatten.snd) m w
  | tag _ f,      flatten, m, w => spaceUptoLine f flatten m w

private structure WorkItem where
  f : Format
  indent : Int
  activeTags : Nat

private structure WorkGroup where
  flatten : Bool
  flb     : FlattenBehavior
  items   : List WorkItem

private partial def spaceUptoLine' : List WorkGroup → Bool → Nat → Nat → SpaceResult
  |   [], _,                         _,   _ => {}
  |   { items := [],    .. }::gs, _, col, w => spaceUptoLine' gs false col w
  | g@{ items := i::is, .. }::gs, subFlatten, col, w =>
    merge w
      (spaceUptoLine i.f (g.flatten, subFlatten) (w + col - i.indent) w)
      (spaceUptoLine' ({ g with items := is }::gs) subFlatten col)

private def pushGroup (flb : FlattenBehavior) (items : List WorkItem) (gs : List WorkGroup) (w : Nat) [Monad m] [MonadPrettyFormat m] : m (List WorkGroup) := do
  let k  ← currColumn
  -- Flatten group if it + the remainder (gs) fits in the remaining space. For `fill`, measure only up to the next (ungrouped) line break.
  let g  := { flatten := flb == FlattenBehavior.allOrNone, flb := flb, items := items : WorkGroup }
  let r  := spaceUptoLine' [g] true k (w-k)
  let r' := merge (w-k) r (spaceUptoLine' gs false k)
  -- Prevent flattening if any item contains a hard line break, except within `fill` if it is ungrouped (=> unflattened)
  return { g with flatten := !r.foundFlattenedHardLine && r'.space <= w-k }::gs

private partial def be (w : Nat) [Monad m] [MonadPrettyFormat m] : List WorkGroup → m Unit
  | []                           => pure ()
  |   { items := [],    .. }::gs => be w gs
  | g@{ items := i::is, .. }::gs => do
    let gs' (is' : List WorkItem) := { g with items := is' }::gs;
    match i.f with
    | nil =>
      endTags i.activeTags
      be w (gs' is)
    | tag t f =>
      startTag t
      be w (gs' ({ i with f, activeTags := i.activeTags + 1 }::is))
    | append f₁ f₂ => be w (gs' ({ i with f := f₁, activeTags := 0 }::{ i with f := f₂ }::is))
    | nest n f => be w (gs' ({ i with f, indent := i.indent + n }::is))
    | text s =>
      let p := s.posOf '\n'
      if p == s.endPos then
        pushOutput s
        endTags i.activeTags
        be w (gs' is)
      else
        pushOutput (s.extract {} p)
        pushNewline i.indent.toNat
        let is := { i with f := text (s.extract (s.next p) s.endPos) }::is
        -- after a hard line break, re-evaluate whether to flatten the remaining group
        pushGroup g.flb is gs w >>= be w
    | line =>
      match g.flb with
      | FlattenBehavior.allOrNone =>
        if g.flatten then
          -- flatten line = text " "
          pushOutput " "
          endTags i.activeTags
          be w (gs' is)
        else
          pushNewline i.indent.toNat
          endTags i.activeTags
          be w (gs' is)
      | FlattenBehavior.fill =>
        let breakHere := do
          pushNewline i.indent.toNat
          -- make new `fill` group and recurse
          endTags i.activeTags
          pushGroup FlattenBehavior.fill is gs w >>= be w
        -- if preceding fill item fit in a single line, try to fit next one too
        if g.flatten then
          let gs'@(g'::_) ← pushGroup FlattenBehavior.fill is gs (w - " ".length)
            | panic "unreachable"
          if g'.flatten then
            pushOutput " "
            endTags i.activeTags
            be w gs'  -- TODO: use `return`
          else
            breakHere
        else
          breakHere
    | align force =>
      if g.flatten && !force then
        -- flatten (align false) = nil
        endTags i.activeTags
        be w (gs' is)
      else
        let k ← currColumn
        if k < i.indent then
          pushOutput ("".pushn ' ' (i.indent - k).toNat)
          endTags i.activeTags
          be w (gs' is)
        else
          pushNewline i.indent.toNat
          endTags i.activeTags
          be w (gs' is)
    | group f flb =>
      if g.flatten then
        -- flatten (group f) = flatten f
        be w (gs' ({ i with f }::is))
      else
        pushGroup flb [{ i with f }] (gs' is) w >>= be w

/-- Render the given `f : Format` with a line width of `w`.
`indent` is the starting amount to indent each line by. -/
def prettyM (f : Format) (w : Nat) (indent : Nat := 0) [Monad m] [MonadPrettyFormat m] : m Unit :=
  be w [{ flb := FlattenBehavior.allOrNone, flatten := false, items := [{ f := f, indent, activeTags := 0 }]}]
