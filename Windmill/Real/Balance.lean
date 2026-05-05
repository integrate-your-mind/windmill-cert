import Windmill.Real.State

noncomputable section

open Classical

namespace Windmill
namespace Real

def NearBalanced (left right : ℕ) : Prop :=
  left = right ∨ left + 1 = right ∨ right + 1 = left

namespace NearBalanced

lemma refl (n : ℕ) : NearBalanced n n :=
  Or.inl rfl

lemma symm {left right : ℕ} (h : NearBalanced left right) :
    NearBalanced right left := by
  rcases h with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

end NearBalanced

namespace Line

def physicalLeftIndices {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ≠ pivot ∧ IsLeft line (pts i)

def physicalRightIndices {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ≠ pivot ∧ IsRight line (pts i)

def physicalLeftCount {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) : ℕ :=
  (physicalLeftIndices pts line pivot).card

def physicalRightCount {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) : ℕ :=
  (physicalRightIndices pts line pivot).card

def throughPivot {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) : Prop :=
  contains line (pts pivot)

def PhysicallyBalanced {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) : Prop :=
  throughPivot pts line pivot ∧
    NearBalanced
      (physicalLeftCount pts line pivot)
      (physicalRightCount pts line pivot)

lemma physicalLeftIndices_reverse {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) :
    physicalLeftIndices pts (reverse line) pivot =
      physicalRightIndices pts line pivot := by
  unfold physicalLeftIndices physicalRightIndices
  apply Finset.filter_congr
  intro i _
  rw [isLeft_reverse_iff_isRight]

lemma physicalRightIndices_reverse {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) :
    physicalRightIndices pts (reverse line) pivot =
      physicalLeftIndices pts line pivot := by
  unfold physicalLeftIndices physicalRightIndices
  apply Finset.filter_congr
  intro i _
  rw [isRight_reverse_iff_isLeft]

lemma physicalLeftCount_reverse {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) :
    physicalLeftCount pts (reverse line) pivot =
      physicalRightCount pts line pivot := by
  unfold physicalLeftCount physicalRightCount
  rw [physicalLeftIndices_reverse]

lemma physicalRightCount_reverse {n : ℕ} (pts : PointConfig n)
    (line : Line) (pivot : Fin n) :
    physicalRightCount pts (reverse line) pivot =
      physicalLeftCount pts line pivot := by
  unfold physicalLeftCount physicalRightCount
  rw [physicalRightIndices_reverse]

end Line

namespace WState

def strictLeftIndices {n : ℕ} (pts : PointConfig n)
    (state : WState n) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    i ≠ state.curr ∧ i ≠ state.prev ∧
      Line.IsLeft (rayLine pts state) (pts i)

def strictRightIndices {n : ℕ} (pts : PointConfig n)
    (state : WState n) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    i ≠ state.curr ∧ i ≠ state.prev ∧
      Line.IsRight (rayLine pts state) (pts i)

def strictLeftCount {n : ℕ} (pts : PointConfig n)
    (state : WState n) : ℕ :=
  (strictLeftIndices pts state).card

def strictRightCount {n : ℕ} (pts : PointConfig n)
    (state : WState n) : ℕ :=
  (strictRightIndices pts state).card

def postSwitchLeftCount {n : ℕ} (pts : PointConfig n)
    (state : WState n) (entering : Side) : ℕ :=
  strictLeftCount pts state +
    match entering with
    | Side.left => 1
    | Side.right => 0

def postSwitchRightCount {n : ℕ} (pts : PointConfig n)
    (state : WState n) (entering : Side) : ℕ :=
  strictRightCount pts state +
    match entering with
    | Side.left => 0
    | Side.right => 1

def PostSwitchBalanced {n : ℕ} (pts : PointConfig n)
    (state : WState n) (entering : Side) : Prop :=
  NearBalanced
    (postSwitchLeftCount pts state entering)
    (postSwitchRightCount pts state entering)

end WState

end Real
end Windmill
