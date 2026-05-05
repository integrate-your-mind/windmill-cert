import Windmill.Universal.Primitives

namespace Windmill
namespace Universal

inductive Side where
  | left
  | right
deriving Repr, DecidableEq, Inhabited

namespace Side

def sign : Side -> Int
  | left => 1
  | right => -1

def reverse : Side -> Side
  | left => right
  | right => left

def ofSign (z : Int) : Option Side :=
  if z > 0 then
    some left
  else if z < 0 then
    some right
  else
    none

@[simp] theorem sign_reverse (side : Side) : sign (reverse side) = -sign side := by
  cases side <;> rfl

end Side

namespace Point

def sideSign (a b p : Point) : Int :=
  orient a b p

def side (a b p : Point) : Option Side :=
  Side.ofSign (sideSign a b p)

def IsLeft (a b p : Point) : Prop :=
  sideSign a b p > 0

def IsRight (a b p : Point) : Prop :=
  sideSign a b p < 0

theorem orient_line_reversal_neg (a b p : Point) :
    orient b a p = -orient a b p :=
  orient_line_reversal a b p

theorem sideSign_line_reversal (a b p : Point) :
    sideSign b a p = -sideSign a b p := by
  unfold sideSign
  exact orient_line_reversal a b p

theorem isLeft_line_reversal_iff_isRight (a b p : Point) :
    IsLeft b a p <-> IsRight a b p := by
  unfold IsLeft IsRight sideSign
  rw [orient_line_reversal]
  constructor <;> intro h <;> omega

theorem isRight_line_reversal_iff_isLeft (a b p : Point) :
    IsRight b a p <-> IsLeft a b p := by
  unfold IsRight IsLeft sideSign
  rw [orient_line_reversal]
  constructor <;> intro h <;> omega

theorem side_eq_left_iff_isLeft (a b p : Point) :
    side a b p = some Side.left <-> IsLeft a b p := by
  unfold side Side.ofSign IsLeft sideSign
  by_cases hpos : orient a b p > 0
  · simp [hpos]
  · by_cases hneg : orient a b p < 0
    · simp [hpos, hneg]
    · simp [hpos, hneg]

theorem side_eq_right_iff_isRight (a b p : Point) :
    side a b p = some Side.right <-> IsRight a b p := by
  unfold side Side.ofSign IsRight sideSign
  by_cases hpos : orient a b p > 0
  · simp [hpos]
    omega
  · by_cases hneg : orient a b p < 0
    · simp [hpos, hneg]
    · simp [hpos, hneg]

theorem side_eq_none_iff_collinear (a b p : Point) :
    side a b p = none <-> Collinear a b p := by
  unfold side Side.ofSign Collinear sideSign
  by_cases hpos : orient a b p > 0
  · simp [hpos]
    omega
  · by_cases hneg : orient a b p < 0
    · simp [hpos, hneg]
      omega
    · simp [hpos, hneg]
      omega

theorem not_isLeft_of_collinear {a b p : Point} (h : Collinear a b p) :
    ¬ IsLeft a b p := by
  unfold Collinear at h
  unfold IsLeft sideSign
  omega

theorem not_isRight_of_collinear {a b p : Point} (h : Collinear a b p) :
    ¬ IsRight a b p := by
  unfold Collinear at h
  unfold IsRight sideSign
  omega

theorem collinear_neither_left_nor_right {a b p : Point} (h : Collinear a b p) :
    ¬ IsLeft a b p ∧ ¬ IsRight a b p :=
  And.intro (not_isLeft_of_collinear h) (not_isRight_of_collinear h)

end Point

namespace Line

def sideSign (line : Line) (p : Point) : Int :=
  Point.sideSign line.a line.b p

def side (line : Line) (p : Point) : Option Side :=
  Point.side line.a line.b p

def IsLeft (line : Line) (p : Point) : Prop :=
  Point.IsLeft line.a line.b p

def IsRight (line : Line) (p : Point) : Prop :=
  Point.IsRight line.a line.b p

theorem sideSign_reverse (line : Line) (p : Point) :
    sideSign (reverse line) p = -sideSign line p := by
  cases line
  unfold sideSign reverse
  exact Point.sideSign_line_reversal _ _ p

theorem isLeft_reverse_iff_isRight (line : Line) (p : Point) :
    IsLeft (reverse line) p <-> IsRight line p := by
  cases line
  unfold IsLeft IsRight reverse
  exact Point.isLeft_line_reversal_iff_isRight _ _ p

theorem isRight_reverse_iff_isLeft (line : Line) (p : Point) :
    IsRight (reverse line) p <-> IsLeft line p := by
  cases line
  unfold IsRight IsLeft reverse
  exact Point.isRight_line_reversal_iff_isLeft _ _ p

theorem not_isLeft_of_contains {line : Line} {p : Point} (h : contains line p) :
    ¬ IsLeft line p := by
  unfold contains at h
  unfold IsLeft
  exact Point.not_isLeft_of_collinear h

theorem not_isRight_of_contains {line : Line} {p : Point} (h : contains line p) :
    ¬ IsRight line p := by
  unfold contains at h
  unfold IsRight
  exact Point.not_isRight_of_collinear h

theorem contains_neither_left_nor_right {line : Line} {p : Point} (h : contains line p) :
    ¬ IsLeft line p ∧ ¬ IsRight line p :=
  And.intro (not_isLeft_of_contains h) (not_isRight_of_contains h)

theorem side_eq_left_iff_isLeft (line : Line) (p : Point) :
    side line p = some Side.left <-> IsLeft line p := by
  cases line
  exact Point.side_eq_left_iff_isLeft _ _ p

theorem side_eq_right_iff_isRight (line : Line) (p : Point) :
    side line p = some Side.right <-> IsRight line p := by
  cases line
  exact Point.side_eq_right_iff_isRight _ _ p

theorem side_eq_none_iff_contains (line : Line) (p : Point) :
    side line p = none <-> contains line p := by
  cases line
  exact Point.side_eq_none_iff_collinear _ _ p

end Line

end Universal
end Windmill
