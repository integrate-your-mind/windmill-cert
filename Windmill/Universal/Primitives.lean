namespace Windmill
namespace Universal

structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq, Inhabited

structure Vec where
  dx : Int
  dy : Int
deriving Repr, DecidableEq, Inhabited

namespace Vec

def neg (u : Vec) : Vec :=
  { dx := -u.dx, dy := -u.dy }

def cross (u v : Vec) : Int :=
  u.dx * v.dy - u.dy * v.dx

theorem cross_antisymm (u v : Vec) : cross v u = -cross u v := by
  unfold cross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

theorem cross_self (u : Vec) : cross u u = 0 := by
  unfold cross
  simp [Int.mul_comm]

theorem cross_left_neg (u v : Vec) : cross (neg u) v = -cross u v := by
  unfold cross neg
  simp [Int.sub_eq_add_neg, Int.neg_mul]
  omega

theorem cross_right_neg (u v : Vec) : cross u (neg v) = -cross u v := by
  unfold cross neg
  simp [Int.sub_eq_add_neg, Int.mul_neg]
  omega

end Vec

namespace Point

def sub (a b : Point) : Vec :=
  { dx := a.x - b.x, dy := a.y - b.y }

def displacement (a b : Point) : Vec :=
  sub b a

def edgeCross (a b : Point) : Int :=
  a.x * b.y - a.y * b.x

def orient (a b c : Point) : Int :=
  edgeCross a b + edgeCross b c + edgeCross c a

def Collinear (a b c : Point) : Prop :=
  orient a b c = 0

theorem edgeCross_antisymm (a b : Point) : edgeCross b a = -edgeCross a b := by
  unfold edgeCross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

theorem orient_eq_cross_sub (a b c : Point) :
    orient a b c = Vec.cross (sub b a) (sub c a) := by
  unfold orient edgeCross Vec.cross sub
  simp [Int.sub_eq_add_neg, Int.mul_add, Int.mul_comm, Int.mul_neg, Int.neg_add]
  omega

theorem orient_cyclic (a b c : Point) : orient a b c = orient b c a := by
  unfold orient
  omega

theorem orient_cyclic' (a b c : Point) : orient a b c = orient c a b := by
  rw [orient_cyclic, orient_cyclic]

theorem orient_swap_last (a b c : Point) : orient a c b = -orient a b c := by
  unfold orient edgeCross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

theorem orient_swap_first_two (a b c : Point) : orient b a c = -orient a b c := by
  unfold orient edgeCross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

theorem orient_line_reversal (a b p : Point) : orient b a p = -orient a b p :=
  orient_swap_first_two a b p

@[simp] theorem orient_self_left (a b : Point) : orient a a b = 0 := by
  unfold orient edgeCross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

@[simp] theorem orient_self_middle (a b : Point) : orient a b a = 0 := by
  unfold orient edgeCross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

@[simp] theorem orient_self_right (a b : Point) : orient a b b = 0 := by
  unfold orient edgeCross
  simp [Int.sub_eq_add_neg, Int.mul_comm]
  omega

theorem collinear_cyclic {a b c : Point} (h : Collinear a b c) :
    Collinear b c a := by
  unfold Collinear at h
  unfold Collinear
  rw [<- orient_cyclic]
  exact h

theorem collinear_swap_last {a b c : Point} (h : Collinear a b c) :
    Collinear a c b := by
  unfold Collinear at h
  unfold Collinear
  rw [orient_swap_last, h]
  rfl

theorem collinear_line_reversal {a b p : Point} :
    Collinear b a p <-> Collinear a b p := by
  constructor
  case mp =>
    intro h
    unfold Collinear at h
    unfold Collinear
    rw [orient_line_reversal] at h
    omega
  case mpr =>
    intro h
    unfold Collinear at h
    unfold Collinear
    rw [orient_line_reversal, h]
    rfl

end Point

structure Line where
  a : Point
  b : Point
deriving Repr, DecidableEq, Inhabited

namespace Line

def Nondegenerate (line : Line) : Prop :=
  line.a ≠ line.b

def reverse (line : Line) : Line :=
  { a := line.b, b := line.a }

def contains (line : Line) (p : Point) : Prop :=
  Point.Collinear line.a line.b p

@[simp] theorem contains_reverse (line : Line) (p : Point) :
    contains (reverse line) p <-> contains line p := by
  unfold contains reverse
  exact Point.collinear_line_reversal

theorem nondegenerate_reverse (line : Line) :
    Nondegenerate (reverse line) <-> Nondegenerate line := by
  unfold Nondegenerate reverse
  constructor
  · intro h hline
    exact h hline.symm
  · intro h hline
    exact h hline.symm

end Line

end Universal
end Windmill
