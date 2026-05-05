import Windmill.Real.Primitives

noncomputable section

namespace Windmill
namespace Real

abbrev PointConfig (n : ℕ) := Fin n → Point

def Distinct {n : ℕ} (pts : PointConfig n) : Prop :=
  Function.Injective pts

def NoThreeCollinear {n : ℕ} (pts : PointConfig n) : Prop :=
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    ¬ Collinear (pts i) (pts j) (pts k)

structure GeneralPosition {n : ℕ} (pts : PointConfig n) : Prop where
  distinct : Distinct pts
  no_three_collinear : NoThreeCollinear pts

namespace GeneralPosition

lemma injective {n : ℕ} {pts : PointConfig n}
    (h : GeneralPosition pts) : Function.Injective pts :=
  h.distinct

lemma point_ne {n : ℕ} {pts : PointConfig n}
    (h : GeneralPosition pts) {i j : Fin n} (hij : i ≠ j) :
    pts i ≠ pts j := by
  exact fun hp => hij (h.injective hp)

lemma not_collinear {n : ℕ} {pts : PointConfig n}
    (h : GeneralPosition pts) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear (pts i) (pts j) (pts k) :=
  h.no_three_collinear i j k hij hik hjk

lemma orient_ne_zero {n : ℕ} {pts : PointConfig n}
    (h : GeneralPosition pts) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orient (pts i) (pts j) (pts k) ≠ 0 := by
  exact h.not_collinear hij hik hjk

lemma not_collinear_perm_last {n : ℕ} {pts : PointConfig n}
    (h : GeneralPosition pts) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ Collinear (pts i) (pts k) (pts j) := by
  intro hc
  exact h.not_collinear hij hik hjk (collinear_swap_last hc)

lemma orient_ne_zero_perm_last {n : ℕ} {pts : PointConfig n}
    (h : GeneralPosition pts) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orient (pts i) (pts k) (pts j) ≠ 0 := by
  exact h.not_collinear_perm_last hij hik hjk

end GeneralPosition

end Real
end Windmill
