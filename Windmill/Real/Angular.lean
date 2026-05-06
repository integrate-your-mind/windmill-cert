import Windmill.Real.Arc
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

noncomputable section

open Classical
open scoped EuclideanGeometry RealInnerProductSpace
open scoped EuclideanSpace

namespace Windmill
namespace Real

abbrev EPoint := EuclideanSpace ℝ (Fin 2)

local instance : Module.Oriented ℝ EPoint (Fin 2) where
  positiveOrientation := ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).orientation

def toEPoint (p : Point) : EPoint :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2]

def orientedAngle (pivot start target : Point) : Real.Angle :=
  EuclideanGeometry.oangle
    (V := EPoint) (P := EPoint)
    (toEPoint start) (toEPoint pivot) (toEPoint target)

def orientedAngleReal (pivot start target : Point) : ℝ :=
  (orientedAngle pivot start target).toReal

/--
The positive angular displacement from the ray `pivot -> start` to the ray
`pivot -> target`, folded into one open half-turn. Endpoint/nondegeneracy
facts are proved separately; this definition is just the numeric order key.
-/
def halfTurnParam (pivot start target : Point) : ℝ :=
  let θ := orientedAngleReal pivot start target
  if 0 < θ then θ else θ + Real.pi

def angleCandidateSet {n : ℕ} (state : WState n) : Finset (Fin n) :=
  Finset.univ.filter fun i => i ≠ state.curr ∧ i ≠ state.prev

lemma mem_angleCandidateSet {n : ℕ} {state : WState n} {i : Fin n} :
    i ∈ angleCandidateSet state ↔ i ≠ state.curr ∧ i ≠ state.prev := by
  unfold angleCandidateSet
  simp

lemma angleCandidateSet_nonempty {n : ℕ} (state : WState n)
    (hn : 3 ≤ n) :
    (angleCandidateSet state).Nonempty := by
  classical
  let blocked : Finset (Fin n) := {state.curr, state.prev}
  have hcurr_not_mem : state.curr ∉ ({state.prev} : Finset (Fin n)) := by
    simp [state.curr_ne_prev]
  have hblocked_card : blocked.card = 2 := by
    unfold blocked
    rw [Finset.card_insert_of_notMem hcurr_not_mem]
    simp
  have hlt : blocked.card < (Finset.univ : Finset (Fin n)).card := by
    rw [hblocked_card, Finset.card_univ, Fintype.card_fin]
    exact hn
  obtain ⟨i, _hi_univ, hi_not_blocked⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := blocked)
      (t := (Finset.univ : Finset (Fin n))) hlt
  refine ⟨i, ?_⟩
  rw [mem_angleCandidateSet]
  unfold blocked at hi_not_blocked
  simpa [Finset.mem_insert, Finset.mem_singleton] using hi_not_blocked

def stateHalfTurnParam {n : ℕ} (pts : PointConfig n)
    (state : WState n) (target : Fin n) : ℝ :=
  halfTurnParam (pts state.curr) (pts state.prev) (pts target)

def IsAngleNextPivot {n : ℕ} (pts : PointConfig n)
    (state : WState n) (next : Fin n) : Prop :=
  next ∈ angleCandidateSet state ∧
    ∀ test : Fin n, test ∈ angleCandidateSet state →
      stateHalfTurnParam pts state next ≤ stateHalfTurnParam pts state test

theorem angle_nextPivot_exists {n : ℕ} (pts : PointConfig n)
    (state : WState n) (hn : 3 ≤ n) :
    ∃ next : Fin n, IsAngleNextPivot pts state next := by
  classical
  obtain ⟨next, hnext_mem, hnext_min⟩ :=
    Finset.exists_min_image (angleCandidateSet state)
      (stateHalfTurnParam pts state) (angleCandidateSet_nonempty state hn)
  exact ⟨next, hnext_mem, hnext_min⟩

theorem angle_nextPivot_unique_of_param_injective {n : ℕ}
    (pts : PointConfig n) (state : WState n)
    (hinj : ∀ ⦃i j : Fin n⦄,
      i ∈ angleCandidateSet state →
      j ∈ angleCandidateSet state →
      stateHalfTurnParam pts state i = stateHalfTurnParam pts state j →
        i = j)
    {a b : Fin n}
    (ha : IsAngleNextPivot pts state a)
    (hb : IsAngleNextPivot pts state b) :
    a = b := by
  have hab : stateHalfTurnParam pts state a =
      stateHalfTurnParam pts state b := by
    exact le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)
  exact hinj ha.1 hb.1 hab

end Real
end Windmill
