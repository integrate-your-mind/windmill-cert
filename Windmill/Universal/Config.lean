import Windmill.Universal.Primitives

namespace Windmill
namespace Universal

/-- A finite point configuration indexed by `Fin n`. -/
structure PointConfig (n : Nat) where
  points : Fin n -> Point

namespace PointConfig

instance {n : Nat} : CoeFun (PointConfig n) (fun _ => Fin n -> Point) where
  coe cfg := cfg.points

/-- The point map has no repeated values. -/
def Injective {n : Nat} (cfg : PointConfig n) : Prop :=
  Function.Injective cfg.points

/-- Geometric name for injectivity of the finite point map. -/
def Distinct {n : Nat} (cfg : PointConfig n) : Prop :=
  cfg.Injective

/-- Equivalent pointwise form: distinct indices have distinct point values. -/
def PointValuesDistinct {n : Nat} (cfg : PointConfig n) : Prop :=
  forall {i j : Fin n}, Ne i j -> Ne (cfg i) (cfg j)

theorem distinct_iff_injective {n : Nat} {cfg : PointConfig n} :
    cfg.Distinct <-> cfg.Injective :=
  Iff.rfl

theorem injective_of_distinct {n : Nat} {cfg : PointConfig n}
    (h : cfg.Distinct) : cfg.Injective :=
  h

theorem distinct_of_injective {n : Nat} {cfg : PointConfig n}
    (h : cfg.Injective) : cfg.Distinct :=
  h

theorem point_eq_index_eq_of_distinct {n : Nat} {cfg : PointConfig n}
    (h : cfg.Distinct) {i j : Fin n} (hp : cfg i = cfg j) : i = j :=
  h hp

theorem point_ne_of_distinct {n : Nat} {cfg : PointConfig n}
    (h : cfg.Distinct) {i j : Fin n} (hij : Ne i j) : Ne (cfg i) (cfg j) := by
  intro hp
  exact hij (point_eq_index_eq_of_distinct h hp)

theorem pointValuesDistinct_of_distinct {n : Nat} {cfg : PointConfig n}
    (h : cfg.Distinct) : cfg.PointValuesDistinct := by
  intro i j hij
  exact point_ne_of_distinct h hij

theorem distinct_of_pointValuesDistinct {n : Nat} {cfg : PointConfig n}
    (h : cfg.PointValuesDistinct) : cfg.Distinct := by
  intro i j hp
  by_cases hij : i = j
  case pos =>
    exact hij
  case neg =>
    exact False.elim (h hij hp)

theorem distinct_iff_pointValuesDistinct {n : Nat} {cfg : PointConfig n} :
    cfg.Distinct <-> cfg.PointValuesDistinct := by
  constructor
  case mp =>
    exact pointValuesDistinct_of_distinct
  case mpr =>
    exact distinct_of_pointValuesDistinct

end PointConfig

/-- No three pairwise-distinct indices select collinear point values. -/
def NoThreeCollinear {n : Nat} (cfg : PointConfig n) : Prop :=
  forall {i j k : Fin n}, Ne i j -> Ne j k -> Ne k i ->
    Not (Point.Collinear (cfg i) (cfg j) (cfg k))

/-- A finite point configuration in general position. -/
structure GeneralPosition {n : Nat} (cfg : PointConfig n) : Prop where
  distinct : cfg.Distinct
  no_three_collinear : NoThreeCollinear cfg

namespace GeneralPosition

theorem injective {n : Nat} {cfg : PointConfig n}
    (h : GeneralPosition cfg) : cfg.Injective :=
  PointConfig.injective_of_distinct h.distinct

theorem point_ne {n : Nat} {cfg : PointConfig n}
    (h : GeneralPosition cfg) {i j : Fin n} (hij : Ne i j) :
    Ne (cfg i) (cfg j) :=
  PointConfig.point_ne_of_distinct h.distinct hij

theorem not_collinear {n : Nat} {cfg : PointConfig n}
    (h : GeneralPosition cfg) {i j k : Fin n}
    (hij : Ne i j) (hjk : Ne j k) (hki : Ne k i) :
    Not (Point.Collinear (cfg i) (cfg j) (cfg k)) :=
  h.no_three_collinear hij hjk hki

/-- Same as `not_collinear`, with the two inequalities involving `i` grouped first. -/
theorem not_collinear_of_ne {n : Nat} {cfg : PointConfig n}
    (h : GeneralPosition cfg) {i j k : Fin n}
    (hij : Ne i j) (hik : Ne i k) (hjk : Ne j k) :
    Not (Point.Collinear (cfg i) (cfg j) (cfg k)) :=
  h.not_collinear hij hjk (fun hki => hik hki.symm)

theorem orient_ne_zero {n : Nat} {cfg : PointConfig n}
    (h : GeneralPosition cfg) {i j k : Fin n}
    (hij : Ne i j) (hjk : Ne j k) (hki : Ne k i) :
    Ne (Point.orient (cfg i) (cfg j) (cfg k)) 0 :=
  h.not_collinear hij hjk hki

theorem orient_ne_zero_of_ne {n : Nat} {cfg : PointConfig n}
    (h : GeneralPosition cfg) {i j k : Fin n}
    (hij : Ne i j) (hik : Ne i k) (hjk : Ne j k) :
    Ne (Point.orient (cfg i) (cfg j) (cfg k)) 0 :=
  h.not_collinear_of_ne hij hik hjk

end GeneralPosition

end Universal
end Windmill
