import Windmill.Real.Config

noncomputable section

open Classical

namespace Windmill
namespace Real

inductive Side where
  | left
  | right
deriving Repr, DecidableEq, Inhabited

namespace Side

def reverse : Side → Side
  | left => right
  | right => left

@[simp] lemma reverse_reverse (side : Side) :
    reverse (reverse side) = side := by
  cases side <;> rfl

end Side

namespace Point

def sideSign (a b p : Point) : ℝ :=
  orient a b p

def IsLeft (a b p : Point) : Prop :=
  sideSign a b p > 0

def IsRight (a b p : Point) : Prop :=
  sideSign a b p < 0

def side (a b p : Point) : Option Side :=
  if IsLeft a b p then
    some Side.left
  else if IsRight a b p then
    some Side.right
  else
    none

lemma sideSign_line_reversal (a b p : Point) :
    sideSign b a p = -sideSign a b p := by
  unfold sideSign
  exact orient_line_reversal a b p

lemma isLeft_line_reversal_iff_isRight (a b p : Point) :
    IsLeft b a p ↔ IsRight a b p := by
  unfold IsLeft IsRight sideSign
  rw [orient_line_reversal]
  constructor <;> intro h <;> linarith

lemma isRight_line_reversal_iff_isLeft (a b p : Point) :
    IsRight b a p ↔ IsLeft a b p := by
  unfold IsRight IsLeft sideSign
  rw [orient_line_reversal]
  constructor <;> intro h <;> linarith

lemma not_isLeft_of_collinear {a b p : Point} (h : Collinear a b p) :
    ¬ IsLeft a b p := by
  unfold Collinear at h
  unfold IsLeft sideSign
  linarith

lemma not_isRight_of_collinear {a b p : Point} (h : Collinear a b p) :
    ¬ IsRight a b p := by
  unfold Collinear at h
  unfold IsRight sideSign
  linarith

lemma collinear_neither_left_nor_right {a b p : Point} (h : Collinear a b p) :
    ¬ IsLeft a b p ∧ ¬ IsRight a b p :=
  And.intro (not_isLeft_of_collinear h) (not_isRight_of_collinear h)

lemma side_eq_left_iff_isLeft (a b p : Point) :
    side a b p = some Side.left ↔ IsLeft a b p := by
  unfold side
  by_cases hleft : IsLeft a b p
  · simp [hleft]
  · by_cases hright : IsRight a b p
    · simp [hleft, hright]
    · simp [hleft, hright]

lemma side_eq_right_iff_isRight (a b p : Point) :
    side a b p = some Side.right ↔ IsRight a b p := by
  unfold side
  by_cases hleft : IsLeft a b p
  · have hnotRight : ¬ IsRight a b p := by
      unfold IsLeft sideSign at hleft
      unfold IsRight sideSign
      linarith
    simp [hleft, hnotRight]
  · by_cases hright : IsRight a b p
    · simp [hleft, hright]
    · simp [hleft, hright]

lemma side_eq_none_iff_collinear (a b p : Point) :
    side a b p = none ↔ Collinear a b p := by
  unfold side Collinear IsLeft IsRight sideSign
  by_cases hpos : orient a b p > 0
  · simp [hpos]
    linarith
  · by_cases hneg : orient a b p < 0
    · simp [hpos, hneg]
      linarith
    · simp [hpos, hneg]
      linarith

lemma strict_side_classification {a b p : Point}
    (h : ¬ Collinear a b p) :
    IsLeft a b p ∨ IsRight a b p := by
  unfold Collinear at h
  unfold IsLeft IsRight sideSign
  by_cases hpos : orient a b p > 0
  · exact Or.inl hpos
  · exact Or.inr (lt_of_le_of_ne (not_lt.mp hpos) h)

end Point

namespace Line

def sideSign (line : Line) (p : Point) : ℝ :=
  Point.sideSign line.a line.b p

def IsLeft (line : Line) (p : Point) : Prop :=
  Point.IsLeft line.a line.b p

def IsRight (line : Line) (p : Point) : Prop :=
  Point.IsRight line.a line.b p

def side (line : Line) (p : Point) : Option Side :=
  Point.side line.a line.b p

def leftIndices {n : ℕ} (pts : PointConfig n) (line : Line) : Finset (Fin n) :=
  Finset.univ.filter fun i => IsLeft line (pts i)

def rightIndices {n : ℕ} (pts : PointConfig n) (line : Line) : Finset (Fin n) :=
  Finset.univ.filter fun i => IsRight line (pts i)

def leftCount {n : ℕ} (pts : PointConfig n) (line : Line) : ℕ :=
  (leftIndices pts line).card

def rightCount {n : ℕ} (pts : PointConfig n) (line : Line) : ℕ :=
  (rightIndices pts line).card

lemma sideSign_reverse (line : Line) (p : Point) :
    sideSign (reverse line) p = -sideSign line p := by
  cases line
  unfold sideSign reverse
  exact Point.sideSign_line_reversal _ _ p

lemma isLeft_reverse_iff_isRight (line : Line) (p : Point) :
    IsLeft (reverse line) p ↔ IsRight line p := by
  cases line
  unfold IsLeft IsRight reverse
  exact Point.isLeft_line_reversal_iff_isRight _ _ p

lemma isRight_reverse_iff_isLeft (line : Line) (p : Point) :
    IsRight (reverse line) p ↔ IsLeft line p := by
  cases line
  unfold IsRight IsLeft reverse
  exact Point.isRight_line_reversal_iff_isLeft _ _ p

lemma not_isLeft_of_contains {line : Line} {p : Point} (h : contains line p) :
    ¬ IsLeft line p := by
  cases line
  unfold contains at h
  unfold IsLeft
  exact Point.not_isLeft_of_collinear h

lemma not_isRight_of_contains {line : Line} {p : Point} (h : contains line p) :
    ¬ IsRight line p := by
  cases line
  unfold contains at h
  unfold IsRight
  exact Point.not_isRight_of_collinear h

lemma contains_neither_left_nor_right {line : Line} {p : Point}
    (h : contains line p) :
    ¬ IsLeft line p ∧ ¬ IsRight line p :=
  And.intro (not_isLeft_of_contains h) (not_isRight_of_contains h)

lemma side_eq_left_iff_isLeft (line : Line) (p : Point) :
    side line p = some Side.left ↔ IsLeft line p := by
  cases line
  exact Point.side_eq_left_iff_isLeft _ _ p

lemma side_eq_right_iff_isRight (line : Line) (p : Point) :
    side line p = some Side.right ↔ IsRight line p := by
  cases line
  exact Point.side_eq_right_iff_isRight _ _ p

lemma side_eq_none_iff_contains (line : Line) (p : Point) :
    side line p = none ↔ contains line p := by
  cases line
  exact Point.side_eq_none_iff_collinear _ _ p

lemma leftIndices_reverse {n : ℕ} (pts : PointConfig n) (line : Line) :
    leftIndices pts (reverse line) = rightIndices pts line := by
  unfold leftIndices rightIndices
  apply Finset.filter_congr
  intro i _
  exact isLeft_reverse_iff_isRight line (pts i)

lemma rightIndices_reverse {n : ℕ} (pts : PointConfig n) (line : Line) :
    rightIndices pts (reverse line) = leftIndices pts line := by
  unfold leftIndices rightIndices
  apply Finset.filter_congr
  intro i _
  exact isRight_reverse_iff_isLeft line (pts i)

lemma leftCount_reverse {n : ℕ} (pts : PointConfig n) (line : Line) :
    leftCount pts (reverse line) = rightCount pts line := by
  unfold leftCount rightCount
  rw [leftIndices_reverse]

lemma rightCount_reverse {n : ℕ} (pts : PointConfig n) (line : Line) :
    rightCount pts (reverse line) = leftCount pts line := by
  unfold leftCount rightCount
  rw [rightIndices_reverse]

end Line

end Real
end Windmill
