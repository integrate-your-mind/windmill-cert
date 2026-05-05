namespace Windmill

structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq, Inhabited

structure State where
  prev : Nat
  curr : Nat
deriving Repr, DecidableEq, Inhabited

structure Certificate where
  points : Array Point
  cycle : Array State
  cover : Array Nat
deriving Repr, Inhabited

def area2 (a b c : Point) : Int :=
  (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

def canonicalDirection (a b : Point) : Int × Int :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  if dy < 0 || (dy == 0 && dx < 0) then
    (-dx, -dy)
  else
    (dx, dy)

def crossDir (u v : Int × Int) : Int :=
  u.1 * v.2 - u.2 * v.1

def angleLt (u v : Int × Int) : Bool :=
  crossDir u v > 0

def between (a b c : Int × Int) : Bool :=
  if angleLt a c then
    angleLt a b && angleLt b c
  else
    angleLt a b || angleLt b c

def direction (points : Array Point) (pivot other : Nat) : Int × Int :=
  canonicalDirection (points[pivot]!) (points[other]!)

def stateIndicesValid (points : Array Point) (state : State) : Bool :=
  state.prev < points.size && state.curr < points.size && state.prev != state.curr

def noDuplicates (points : Array Point) : Bool :=
  (List.range points.size).all fun i =>
    ((List.range points.size).drop (i + 1)).all fun j =>
      points[i]! != points[j]!

def noThreeCollinear (points : Array Point) : Bool :=
  (List.range points.size).all fun i =>
    ((List.range points.size).drop (i + 1)).all fun j =>
      ((List.range points.size).drop (j + 1)).all fun k =>
        area2 (points[i]!) (points[j]!) (points[k]!) != 0

def generalPosition (points : Array Point) : Bool :=
  noDuplicates points && noThreeCollinear points

def transitionValid (points : Array Point) (source target : State) : Bool :=
  stateIndicesValid points source &&
    stateIndicesValid points target &&
    target.prev == source.curr &&
    source.prev != target.curr &&
    let a := direction points source.curr source.prev
    let c := direction points source.curr target.curr
    (List.range points.size).all fun idx =>
      if idx == source.curr || idx == source.prev || idx == target.curr then
        true
      else
        !(between a (direction points source.curr idx) c)

def cycleClosed (cert : Certificate) : Bool :=
  cert.cycle.size > 0 &&
    (List.range cert.cycle.size).all fun i =>
      transitionValid
        cert.points
        (cert.cycle[i]!)
        (cert.cycle[(i + 1) % cert.cycle.size]!)

def coverValid (cert : Certificate) : Bool :=
  cert.cover.size == cert.points.size &&
    (List.range cert.points.size).all fun i =>
      let j := cert.cover[i]!
      j < cert.cycle.size && (cert.cycle[j]!).curr == i

def check (cert : Certificate) : Bool :=
  cert.points.size > 1 &&
    generalPosition cert.points &&
    cycleClosed cert &&
    coverValid cert

end Windmill
