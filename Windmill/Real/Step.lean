import Windmill.Real.Arc

noncomputable section

namespace Windmill
namespace Real

def IsNextPivot {n : ℕ} (pts : PointConfig n)
    (state : WState n) (next : Fin n) : Prop :=
  next ≠ state.curr ∧ next ≠ state.prev ∧
    ∀ test : Fin n,
      test ≠ state.curr →
      test ≠ state.prev →
      test ≠ next →
        ¬ InOpenArc
          (pts state.curr)
          (pts state.prev)
          (pts next)
          (pts test)

structure StepWitness {n : ℕ} (pts : PointConfig n)
    (state : WState n) where
  next : Fin n
  is_next : IsNextPivot pts state next

def stepOfWitness {n : ℕ} (pts : PointConfig n)
    (state : WState n) (witness : StepWitness pts state) : WState n :=
  { prev := state.curr
    curr := witness.next
    prev_ne_curr := by
      intro h
      exact witness.is_next.1 h.symm }

lemma stepOfWitness_prev {n : ℕ} (pts : PointConfig n)
    (state : WState n) (witness : StepWitness pts state) :
    (stepOfWitness pts state witness).prev = state.curr :=
  rfl

lemma stepOfWitness_curr {n : ℕ} (pts : PointConfig n)
    (state : WState n) (witness : StepWitness pts state) :
    (stepOfWitness pts state witness).curr = witness.next :=
  rfl

end Real
end Windmill
