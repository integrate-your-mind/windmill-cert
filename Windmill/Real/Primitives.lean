import Mathlib

noncomputable section

namespace Windmill
namespace Real

abbrev Point := ℝ × ℝ

def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def Collinear (a b c : Point) : Prop :=
  orient a b c = 0

lemma orient_antisymm (a b c : Point) :
    orient a c b = -orient a b c := by
  simp [orient]
  ring

lemma orient_cyclic (a b c : Point) :
    orient b c a = orient a b c := by
  simp [orient]
  ring

lemma orient_cyclic' (a b c : Point) :
    orient c a b = orient a b c := by
  exact (orient_cyclic c a b).symm

lemma orient_swap_first_two (a b c : Point) :
    orient b a c = -orient a b c := by
  simp [orient]
  ring

lemma orient_swap_last (a b c : Point) :
    orient a c b = -orient a b c :=
  orient_antisymm a b c

lemma orient_line_reversal (a b p : Point) :
    orient b a p = -orient a b p :=
  orient_swap_first_two a b p

@[simp] lemma orient_self_left (a b : Point) :
    orient a a b = 0 := by
  simp [orient]

@[simp] lemma orient_self_middle (a b : Point) :
    orient a b a = 0 := by
  simp [orient]

@[simp] lemma orient_self_right (a b : Point) :
    orient a b b = 0 := by
  simp [orient]
  ring

lemma collinear_cyclic {a b c : Point} (h : Collinear a b c) :
    Collinear b c a := by
  unfold Collinear at h ⊢
  rw [orient_cyclic]
  exact h

lemma collinear_swap_last {a b c : Point} (h : Collinear a b c) :
    Collinear a c b := by
  unfold Collinear at h ⊢
  rw [orient_swap_last, h]
  simp

lemma collinear_line_reversal {a b p : Point} :
    Collinear b a p ↔ Collinear a b p := by
  unfold Collinear
  rw [orient_line_reversal]
  constructor <;> intro h <;> linarith

structure Line where
  a : Point
  b : Point
deriving DecidableEq

namespace Line

def Nondegenerate (line : Line) : Prop :=
  line.a ≠ line.b

def reverse (line : Line) : Line :=
  { a := line.b, b := line.a }

def contains (line : Line) (p : Point) : Prop :=
  Collinear line.a line.b p

@[simp] lemma reverse_reverse (line : Line) :
    reverse (reverse line) = line := by
  cases line
  rfl

@[simp] lemma contains_reverse (line : Line) (p : Point) :
    contains (reverse line) p ↔ contains line p := by
  cases line
  unfold contains reverse
  exact collinear_line_reversal

lemma nondegenerate_reverse (line : Line) :
    Nondegenerate (reverse line) ↔ Nondegenerate line := by
  unfold Nondegenerate reverse
  constructor
  · intro h hline
    exact h hline.symm
  · intro h hline
    exact h hline.symm

end Line

end Real
end Windmill
