import Windmill.Real.Balance

noncomputable section

open Classical

namespace Windmill
namespace Real

structure Direction where
  dx : ℝ
  dy : ℝ
deriving DecidableEq

namespace Direction

def Nonzero (dir : Direction) : Prop :=
  dir.dx ≠ 0 ∨ dir.dy ≠ 0

def pointAfter (dir : Direction) (p : Point) : Point :=
  (p.1 + dir.dx, p.2 + dir.dy)

def lineThrough (dir : Direction) (p : Point) : Line :=
  { a := p, b := pointAfter dir p }

lemma lineThrough_contains (dir : Direction) (p : Point) :
    Line.contains (lineThrough dir p) p := by
  unfold lineThrough Line.contains
  unfold Collinear
  exact orient_self_middle p (pointAfter dir p)

lemma lineThrough_nondegenerate {dir : Direction} {p : Point}
    (hdir : dir.Nonzero) :
    Line.Nondegenerate (lineThrough dir p) := by
  unfold Nonzero at hdir
  unfold Line.Nondegenerate lineThrough pointAfter
  intro h
  rcases hdir with hdx | hdy
  · have hx := congrArg Prod.fst h
    simp at hx
    exact hdx hx
  · have hy := congrArg Prod.snd h
    simp at hy
    exact hdy hy

end Direction

def height (dir : Direction) (p : Point) : ℝ :=
  dir.dx * p.2 - dir.dy * p.1

lemma orient_lineThrough_eq_height_sub (dir : Direction) (p q : Point) :
    orient p (Direction.pointAfter dir p) q =
      height dir q - height dir p := by
  unfold orient Direction.pointAfter height
  ring

lemma isLeft_lineThrough_iff_height_lt (dir : Direction) (p q : Point) :
    Line.IsLeft (Direction.lineThrough dir p) q ↔
      height dir p < height dir q := by
  unfold Line.IsLeft Point.IsLeft Point.sideSign Direction.lineThrough
  rw [orient_lineThrough_eq_height_sub]
  constructor <;> intro h <;> linarith

lemma isRight_lineThrough_iff_height_lt (dir : Direction) (p q : Point) :
    Line.IsRight (Direction.lineThrough dir p) q ↔
      height dir q < height dir p := by
  unfold Line.IsRight Point.IsRight Point.sideSign Direction.lineThrough
  rw [orient_lineThrough_eq_height_sub]
  constructor <;> intro h <;> linarith

def slopeBad {n : ℕ} (pts : PointConfig n) (pair : Fin n × Fin n) : ℝ :=
  ((pts pair.1).2 - (pts pair.2).2) /
    ((pts pair.1).1 - (pts pair.2).1)

def badSlopePairs {n : ℕ} (pts : PointConfig n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun pair =>
    pair.1 ≠ pair.2 ∧ (pts pair.1).1 ≠ (pts pair.2).1

def badSlopes {n : ℕ} (pts : PointConfig n) : Finset ℝ :=
  (badSlopePairs pts).image (slopeBad pts)

theorem exists_separating_direction {n : ℕ} (pts : PointConfig n)
    (hpts : Distinct pts) :
    ∃ dir : Direction, dir.Nonzero ∧ Function.Injective fun i => height dir (pts i) := by
  classical
  obtain ⟨t, ht⟩ := Finset.exists_notMem (badSlopes pts)
  refine ⟨{ dx := 1, dy := t }, Or.inl one_ne_zero, ?_⟩
  intro i j hij
  unfold height at hij
  simp at hij
  by_cases hx : (pts i).1 = (pts j).1
  · have hy : (pts i).2 = (pts j).2 := by
      rw [hx] at hij
      linarith
    exact hpts (Prod.ext hx hy)
  · have htbad : t ∈ badSlopes pts := by
      unfold badSlopes
      apply Finset.mem_image.mpr
      refine ⟨(i, j), ?_, ?_⟩
      · unfold badSlopePairs
        simp [hx]
        exact fun h => hx (by rw [h])
      · unfold slopeBad
        field_simp [sub_ne_zero.mpr hx]
        linarith
    exact False.elim (ht htbad)

end Real
end Windmill
