import Windmill.Universal.Primitives

namespace Windmill
namespace Universal
namespace TwoPoint

inductive Site where
  | left
  | right
deriving Repr, DecidableEq, Inhabited

namespace Site

def swap : Site -> Site
  | left => right
  | right => left

theorem cases_two (p : Site) : p = left ∨ p = right := by
  cases p <;> simp

@[simp] theorem swap_left : swap left = right := rfl

@[simp] theorem swap_right : swap right = left := rfl

@[simp] theorem swap_swap (p : Site) : swap (swap p) = p := by
  cases p <;> rfl

theorem swap_ne_self (p : Site) : swap p ≠ p := by
  cases p <;> simp [swap]

theorem swap_of_ne {p q : Site} (h : p ≠ q) : swap p = q := by
  cases p <;> cases q <;> simp [swap] at h ⊢

end Site

structure State where
  pivot : Site
deriving Repr, DecidableEq, Inhabited

namespace State

def step (s : State) : State :=
  { pivot := Site.swap s.pivot }

end State

def pivotAt (start : Site) : Nat -> Site
  | 0 => start
  | n + 1 => Site.swap (pivotAt start n)

def stateAt (start : State) : Nat -> State
  | 0 => start
  | n + 1 => State.step (stateAt start n)

theorem pivotAt_zero (start : Site) : pivotAt start 0 = start := rfl

theorem pivotAt_succ (start : Site) (n : Nat) :
    pivotAt start (n + 1) = Site.swap (pivotAt start n) := rfl

theorem pivotAt_two_steps (start : Site) (n : Nat) :
    pivotAt start (n + 2) = pivotAt start n := by
  rw [pivotAt_succ, pivotAt_succ, Site.swap_swap]

theorem stateAt_pivot (start : State) (n : Nat) :
    (stateAt start n).pivot = pivotAt start.pivot n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [stateAt, State.step, pivotAt, ih]

def VisitsInfinitelyOften (start target : Site) : Prop :=
  ∀ lower : Nat, ∃ n : Nat, lower ≤ n ∧ pivotAt start n = target

def StateVisitsInfinitelyOften (start : State) (target : Site) : Prop :=
  ∀ lower : Nat, ∃ n : Nat, lower ≤ n ∧ (stateAt start n).pivot = target

theorem pivotAt_next_of_ne {start target : Site} {n : Nat}
    (h : pivotAt start n ≠ target) :
    pivotAt start (n + 1) = target := by
  rw [pivotAt_succ]
  exact Site.swap_of_ne h

theorem visitsInfinitelyOften (start target : Site) :
    VisitsInfinitelyOften start target := by
  intro lower
  by_cases h : pivotAt start lower = target
  · exact ⟨lower, Nat.le_refl lower, h⟩
  · refine ⟨lower + 1, ?_, ?_⟩
    · exact Nat.le_succ lower
    · exact pivotAt_next_of_ne h

theorem stateVisitsInfinitelyOften (start : State) (target : Site) :
    StateVisitsInfinitelyOften start target := by
  intro lower
  obtain ⟨n, hle, hpivot⟩ := visitsInfinitelyOften start.pivot target lower
  exact ⟨n, hle, by rw [stateAt_pivot, hpivot]⟩

theorem alternatingPivotsVisitBothInfinitelyOften (start : Site) :
    VisitsInfinitelyOften start Site.left ∧ VisitsInfinitelyOften start Site.right := by
  exact ⟨visitsInfinitelyOften start Site.left, visitsInfinitelyOften start Site.right⟩

theorem alternatingStatesVisitBothInfinitelyOften (start : State) :
    StateVisitsInfinitelyOften start Site.left ∧
      StateVisitsInfinitelyOften start Site.right := by
  exact ⟨stateVisitsInfinitelyOften start Site.left,
    stateVisitsInfinitelyOften start Site.right⟩

end TwoPoint
end Universal
end Windmill
