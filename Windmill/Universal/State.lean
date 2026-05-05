import Windmill.Universal.Config
import Windmill.Universal.Side

namespace Windmill
namespace Universal

/--
A discrete windmill state records the previous and current pivot indices.
The distinctness proof keeps the directed state line non-degenerate at the
index level; geometric point distinctness follows from a distinct config.
-/
structure WState (n : Nat) where
  prev : Fin n
  curr : Fin n
  prev_ne_curr : prev ≠ curr

namespace WState

variable {n : Nat}

/-- The previous pivot index. -/
def previousPivotIndex (state : WState n) : Fin n :=
  state.prev

/-- The current pivot index. -/
def currentPivotIndex (state : WState n) : Fin n :=
  state.curr

/-- The previous pivot point in a concrete point configuration. -/
def previousPivot (cfg : PointConfig n) (state : WState n) : Point :=
  cfg state.prev

/-- The current pivot point in a concrete point configuration. -/
def currentPivot (cfg : PointConfig n) (state : WState n) : Point :=
  cfg state.curr

/-- The directed line from the previous pivot to the current pivot. -/
def lineOfState (cfg : PointConfig n) (state : WState n) : Line :=
  { a := previousPivot cfg state, b := currentPivot cfg state }

/-- The same state with the directed line reversed. -/
def reversedState (state : WState n) : WState n :=
  { prev := state.curr
    curr := state.prev
    prev_ne_curr := by
      intro h
      exact state.prev_ne_curr h.symm }

@[simp] theorem previousPivotIndex_eq_prev (state : WState n) :
    previousPivotIndex state = state.prev :=
  rfl

@[simp] theorem currentPivotIndex_eq_curr (state : WState n) :
    currentPivotIndex state = state.curr :=
  rfl

@[simp] theorem previousPivot_eq (cfg : PointConfig n) (state : WState n) :
    previousPivot cfg state = cfg state.prev :=
  rfl

@[simp] theorem currentPivot_eq (cfg : PointConfig n) (state : WState n) :
    currentPivot cfg state = cfg state.curr :=
  rfl

theorem curr_ne_prev (state : WState n) : state.curr ≠ state.prev := by
  intro h
  exact state.prev_ne_curr h.symm

theorem previousPivot_ne_currentPivot {cfg : PointConfig n}
    (hcfg : cfg.Distinct) (state : WState n) :
    previousPivot cfg state ≠ currentPivot cfg state :=
  PointConfig.point_ne_of_distinct hcfg state.prev_ne_curr

theorem currentPivot_ne_previousPivot {cfg : PointConfig n}
    (hcfg : cfg.Distinct) (state : WState n) :
    currentPivot cfg state ≠ previousPivot cfg state := by
  exact (previousPivot_ne_currentPivot hcfg state).symm

@[simp] theorem lineOfState_a (cfg : PointConfig n) (state : WState n) :
    (lineOfState cfg state).a = previousPivot cfg state :=
  rfl

@[simp] theorem lineOfState_b (cfg : PointConfig n) (state : WState n) :
    (lineOfState cfg state).b = currentPivot cfg state :=
  rfl

@[simp] theorem reversedState_prev (state : WState n) :
    (reversedState state).prev = state.curr :=
  rfl

@[simp] theorem reversedState_curr (state : WState n) :
    (reversedState state).curr = state.prev :=
  rfl

theorem reversedState_prev_ne_curr (state : WState n) :
    (reversedState state).prev ≠ (reversedState state).curr :=
  (reversedState state).prev_ne_curr

@[simp] theorem previousPivot_reversedState (cfg : PointConfig n) (state : WState n) :
    previousPivot cfg (reversedState state) = currentPivot cfg state :=
  rfl

@[simp] theorem currentPivot_reversedState (cfg : PointConfig n) (state : WState n) :
    currentPivot cfg (reversedState state) = previousPivot cfg state :=
  rfl

theorem lineOfState_reversedState (cfg : PointConfig n) (state : WState n) :
    lineOfState cfg (reversedState state) = Line.reverse (lineOfState cfg state) :=
  rfl

theorem lineOfState_contains_previousPivot (cfg : PointConfig n) (state : WState n) :
    Line.contains (lineOfState cfg state) (previousPivot cfg state) := by
  unfold Line.contains lineOfState previousPivot currentPivot
  exact Point.orient_self_middle (cfg state.prev) (cfg state.curr)

theorem lineOfState_contains_currentPivot (cfg : PointConfig n) (state : WState n) :
    Line.contains (lineOfState cfg state) (currentPivot cfg state) := by
  unfold Line.contains lineOfState previousPivot currentPivot
  exact Point.orient_self_right (cfg state.prev) (cfg state.curr)

theorem lineOfState_nondegenerate {cfg : PointConfig n}
    (hcfg : cfg.Distinct) (state : WState n) :
    Line.Nondegenerate (lineOfState cfg state) :=
  previousPivot_ne_currentPivot hcfg state

theorem lineOfState_sideSign_reversedState (cfg : PointConfig n)
    (state : WState n) (p : Point) :
    Line.sideSign (lineOfState cfg (reversedState state)) p =
      -Line.sideSign (lineOfState cfg state) p := by
  rw [lineOfState_reversedState]
  exact Line.sideSign_reverse (lineOfState cfg state) p

theorem lineOfState_isLeft_reversedState_iff_isRight (cfg : PointConfig n)
    (state : WState n) (p : Point) :
    Line.IsLeft (lineOfState cfg (reversedState state)) p <->
      Line.IsRight (lineOfState cfg state) p := by
  rw [lineOfState_reversedState]
  exact Line.isLeft_reverse_iff_isRight (lineOfState cfg state) p

theorem lineOfState_isRight_reversedState_iff_isLeft (cfg : PointConfig n)
    (state : WState n) (p : Point) :
    Line.IsRight (lineOfState cfg (reversedState state)) p <->
      Line.IsLeft (lineOfState cfg state) p := by
  rw [lineOfState_reversedState]
  exact Line.isRight_reverse_iff_isLeft (lineOfState cfg state) p

end WState

end Universal
end Windmill
