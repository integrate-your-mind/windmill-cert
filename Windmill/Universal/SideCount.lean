import Windmill.Universal.Config
import Windmill.Universal.Side

namespace Windmill
namespace Universal

namespace PointConfig

/-- Boolean left-side test for an indexed point relative to the oriented pair `a -> b`. -/
def leftIndex {n : Nat} (cfg : PointConfig n) (a b : Point) (i : Fin n) : Bool :=
  decide (Point.sideSign a b (cfg i) > 0)

/-- Boolean right-side test for an indexed point relative to the oriented pair `a -> b`. -/
def rightIndex {n : Nat} (cfg : PointConfig n) (a b : Point) (i : Fin n) : Bool :=
  decide (Point.sideSign a b (cfg i) < 0)

/-- Indices whose points lie strictly left of the oriented pair `a -> b`. -/
def leftIndices {n : Nat} (cfg : PointConfig n) (a b : Point) : List (Fin n) :=
  (List.finRange n).filter (leftIndex cfg a b)

/-- Indices whose points lie strictly right of the oriented pair `a -> b`. -/
def rightIndices {n : Nat} (cfg : PointConfig n) (a b : Point) : List (Fin n) :=
  (List.finRange n).filter (rightIndex cfg a b)

/-- Number of indexed points strictly left of the oriented pair `a -> b`. -/
def leftCount {n : Nat} (cfg : PointConfig n) (a b : Point) : Nat :=
  (List.finRange n).countP (leftIndex cfg a b)

/-- Number of indexed points strictly right of the oriented pair `a -> b`. -/
def rightCount {n : Nat} (cfg : PointConfig n) (a b : Point) : Nat :=
  (List.finRange n).countP (rightIndex cfg a b)

/-- Boolean left-side test for an indexed point relative to an oriented line. -/
def lineLeftIndex {n : Nat} (cfg : PointConfig n) (line : Line) (i : Fin n) : Bool :=
  leftIndex cfg line.a line.b i

/-- Boolean right-side test for an indexed point relative to an oriented line. -/
def lineRightIndex {n : Nat} (cfg : PointConfig n) (line : Line) (i : Fin n) : Bool :=
  rightIndex cfg line.a line.b i

/-- Indices whose points lie strictly left of an oriented line. -/
def lineLeftIndices {n : Nat} (cfg : PointConfig n) (line : Line) : List (Fin n) :=
  leftIndices cfg line.a line.b

/-- Indices whose points lie strictly right of an oriented line. -/
def lineRightIndices {n : Nat} (cfg : PointConfig n) (line : Line) : List (Fin n) :=
  rightIndices cfg line.a line.b

/-- Number of indexed points strictly left of an oriented line. -/
def lineLeftCount {n : Nat} (cfg : PointConfig n) (line : Line) : Nat :=
  leftCount cfg line.a line.b

/-- Number of indexed points strictly right of an oriented line. -/
def lineRightCount {n : Nat} (cfg : PointConfig n) (line : Line) : Nat :=
  rightCount cfg line.a line.b

theorem leftIndex_eq_true_iff {n : Nat} (cfg : PointConfig n)
    (a b : Point) (i : Fin n) :
    leftIndex cfg a b i = true <-> Point.IsLeft a b (cfg i) := by
  unfold leftIndex Point.IsLeft
  simp

theorem rightIndex_eq_true_iff {n : Nat} (cfg : PointConfig n)
    (a b : Point) (i : Fin n) :
    rightIndex cfg a b i = true <-> Point.IsRight a b (cfg i) := by
  unfold rightIndex Point.IsRight
  simp

theorem leftIndex_line_reversal {n : Nat} (cfg : PointConfig n)
    (a b : Point) (i : Fin n) :
    leftIndex cfg b a i = rightIndex cfg a b i := by
  unfold leftIndex rightIndex
  rw [Point.sideSign_line_reversal]
  simp

theorem rightIndex_line_reversal {n : Nat} (cfg : PointConfig n)
    (a b : Point) (i : Fin n) :
    rightIndex cfg b a i = leftIndex cfg a b i := by
  unfold leftIndex rightIndex
  rw [Point.sideSign_line_reversal]
  simp

theorem leftIndices_line_reversal {n : Nat} (cfg : PointConfig n)
    (a b : Point) :
    leftIndices cfg b a = rightIndices cfg a b := by
  unfold leftIndices rightIndices
  apply List.filter_congr
  intro i _hi
  exact leftIndex_line_reversal cfg a b i

theorem rightIndices_line_reversal {n : Nat} (cfg : PointConfig n)
    (a b : Point) :
    rightIndices cfg b a = leftIndices cfg a b := by
  unfold leftIndices rightIndices
  apply List.filter_congr
  intro i _hi
  exact rightIndex_line_reversal cfg a b i

theorem leftCount_line_reversal {n : Nat} (cfg : PointConfig n)
    (a b : Point) :
    leftCount cfg b a = rightCount cfg a b := by
  unfold leftCount rightCount
  apply List.countP_congr
  intro i _hi
  rw [leftIndex_line_reversal]

theorem rightCount_line_reversal {n : Nat} (cfg : PointConfig n)
    (a b : Point) :
    rightCount cfg b a = leftCount cfg a b := by
  unfold leftCount rightCount
  apply List.countP_congr
  intro i _hi
  rw [rightIndex_line_reversal]

theorem lineLeftIndex_reverse {n : Nat} (cfg : PointConfig n)
    (line : Line) (i : Fin n) :
    lineLeftIndex cfg (Line.reverse line) i = lineRightIndex cfg line i := by
  cases line
  exact leftIndex_line_reversal cfg _ _ i

theorem lineRightIndex_reverse {n : Nat} (cfg : PointConfig n)
    (line : Line) (i : Fin n) :
    lineRightIndex cfg (Line.reverse line) i = lineLeftIndex cfg line i := by
  cases line
  exact rightIndex_line_reversal cfg _ _ i

theorem lineLeftIndices_reverse {n : Nat} (cfg : PointConfig n)
    (line : Line) :
    lineLeftIndices cfg (Line.reverse line) = lineRightIndices cfg line := by
  cases line
  exact leftIndices_line_reversal cfg _ _

theorem lineRightIndices_reverse {n : Nat} (cfg : PointConfig n)
    (line : Line) :
    lineRightIndices cfg (Line.reverse line) = lineLeftIndices cfg line := by
  cases line
  exact rightIndices_line_reversal cfg _ _

theorem lineLeftCount_reverse {n : Nat} (cfg : PointConfig n)
    (line : Line) :
    lineLeftCount cfg (Line.reverse line) = lineRightCount cfg line := by
  cases line
  exact leftCount_line_reversal cfg _ _

theorem lineRightCount_reverse {n : Nat} (cfg : PointConfig n)
    (line : Line) :
    lineRightCount cfg (Line.reverse line) = lineLeftCount cfg line := by
  cases line
  exact rightCount_line_reversal cfg _ _

theorem leftIndex_eq_false_of_collinear {n : Nat} (cfg : PointConfig n)
    {a b : Point} {i : Fin n} (h : Point.Collinear a b (cfg i)) :
    leftIndex cfg a b i = false := by
  unfold Point.Collinear at h
  unfold leftIndex Point.sideSign
  rw [h]
  rfl

theorem rightIndex_eq_false_of_collinear {n : Nat} (cfg : PointConfig n)
    {a b : Point} {i : Fin n} (h : Point.Collinear a b (cfg i)) :
    rightIndex cfg a b i = false := by
  unfold Point.Collinear at h
  unfold rightIndex Point.sideSign
  rw [h]
  rfl

theorem not_mem_leftIndices_of_collinear {n : Nat} (cfg : PointConfig n)
    {a b : Point} {i : Fin n} (h : Point.Collinear a b (cfg i)) :
    i ∉ leftIndices cfg a b := by
  intro hi
  have hleft := (List.mem_filter.mp hi).2
  rw [leftIndex_eq_false_of_collinear cfg h] at hleft
  cases hleft

theorem not_mem_rightIndices_of_collinear {n : Nat} (cfg : PointConfig n)
    {a b : Point} {i : Fin n} (h : Point.Collinear a b (cfg i)) :
    i ∉ rightIndices cfg a b := by
  intro hi
  have hright := (List.mem_filter.mp hi).2
  rw [rightIndex_eq_false_of_collinear cfg h] at hright
  cases hright

theorem lineLeftIndex_eq_false_of_contains {n : Nat} (cfg : PointConfig n)
    {line : Line} {i : Fin n} (h : Line.contains line (cfg i)) :
    lineLeftIndex cfg line i = false := by
  unfold lineLeftIndex
  exact leftIndex_eq_false_of_collinear cfg h

theorem lineRightIndex_eq_false_of_contains {n : Nat} (cfg : PointConfig n)
    {line : Line} {i : Fin n} (h : Line.contains line (cfg i)) :
    lineRightIndex cfg line i = false := by
  unfold lineRightIndex
  exact rightIndex_eq_false_of_collinear cfg h

theorem not_mem_lineLeftIndices_of_contains {n : Nat} (cfg : PointConfig n)
    {line : Line} {i : Fin n} (h : Line.contains line (cfg i)) :
    i ∉ lineLeftIndices cfg line := by
  unfold lineLeftIndices
  exact not_mem_leftIndices_of_collinear cfg h

theorem not_mem_lineRightIndices_of_contains {n : Nat} (cfg : PointConfig n)
    {line : Line} {i : Fin n} (h : Line.contains line (cfg i)) :
    i ∉ lineRightIndices cfg line := by
  unfold lineRightIndices
  exact not_mem_rightIndices_of_collinear cfg h

end PointConfig

end Universal
end Windmill
