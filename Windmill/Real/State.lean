import Windmill.Real.Side

noncomputable section

namespace Windmill
namespace Real

structure WState (n : ℕ) where
  prev : Fin n
  curr : Fin n
  prev_ne_curr : prev ≠ curr
deriving DecidableEq

namespace WState

variable {n : ℕ}

def previousPivotIndex (state : WState n) : Fin n :=
  state.prev

def currentPivotIndex (state : WState n) : Fin n :=
  state.curr

def previousPivot (pts : PointConfig n) (state : WState n) : Point :=
  pts state.prev

def currentPivot (pts : PointConfig n) (state : WState n) : Point :=
  pts state.curr

def rayLine (pts : PointConfig n) (state : WState n) : Line :=
  { a := currentPivot pts state, b := previousPivot pts state }

def reversed (state : WState n) : WState n :=
  { prev := state.curr
    curr := state.prev
    prev_ne_curr := by
      intro h
      exact state.prev_ne_curr h.symm }

@[simp] lemma previousPivotIndex_eq (state : WState n) :
    previousPivotIndex state = state.prev :=
  rfl

@[simp] lemma currentPivotIndex_eq (state : WState n) :
    currentPivotIndex state = state.curr :=
  rfl

lemma curr_ne_prev (state : WState n) :
    state.curr ≠ state.prev := by
  intro h
  exact state.prev_ne_curr h.symm

lemma previousPivot_ne_currentPivot {pts : PointConfig n}
    (hpts : Distinct pts) (state : WState n) :
    previousPivot pts state ≠ currentPivot pts state := by
  intro h
  exact state.prev_ne_curr (hpts h)

lemma currentPivot_ne_previousPivot {pts : PointConfig n}
    (hpts : Distinct pts) (state : WState n) :
    currentPivot pts state ≠ previousPivot pts state :=
  (previousPivot_ne_currentPivot hpts state).symm

@[simp] lemma rayLine_a (pts : PointConfig n) (state : WState n) :
    (rayLine pts state).a = currentPivot pts state :=
  rfl

@[simp] lemma rayLine_b (pts : PointConfig n) (state : WState n) :
    (rayLine pts state).b = previousPivot pts state :=
  rfl

lemma rayLine_contains_currentPivot (pts : PointConfig n) (state : WState n) :
    Line.contains (rayLine pts state) (currentPivot pts state) := by
  unfold rayLine currentPivot previousPivot Line.contains
  unfold Collinear
  exact orient_self_middle (pts state.curr) (pts state.prev)

lemma rayLine_contains_previousPivot (pts : PointConfig n) (state : WState n) :
    Line.contains (rayLine pts state) (previousPivot pts state) := by
  unfold rayLine currentPivot previousPivot Line.contains
  unfold Collinear
  exact orient_self_right (pts state.curr) (pts state.prev)

lemma rayLine_nondegenerate {pts : PointConfig n}
    (hpts : Distinct pts) (state : WState n) :
    Line.Nondegenerate (rayLine pts state) := by
  unfold Line.Nondegenerate rayLine
  exact currentPivot_ne_previousPivot hpts state

@[simp] lemma reversed_prev (state : WState n) :
    (reversed state).prev = state.curr :=
  rfl

@[simp] lemma reversed_curr (state : WState n) :
    (reversed state).curr = state.prev :=
  rfl

@[simp] lemma reversed_reversed (state : WState n) :
    reversed (reversed state) = state := by
  cases state
  rfl

lemma rayLine_reversed (pts : PointConfig n) (state : WState n) :
    rayLine pts (reversed state) = Line.reverse (rayLine pts state) := by
  cases state
  rfl

end WState

end Real
end Windmill
