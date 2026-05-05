import Windmill.Real.Projection

noncomputable section

open Classical

namespace Windmill
namespace Real

def lowerCount {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => f j < f i).card

def upperCount {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => f i < f j).card

lemma nearBalanced_median_counts {n : ℕ} (hpos : 0 < n) :
    NearBalanced (n / 2) (n - 1 - n / 2) := by
  unfold NearBalanced
  omega

lemma sorted_lower_count {n : ℕ} (f : Fin n → ℝ)
    (hinj : Function.Injective f) (m : Fin n) :
    lowerCount f ((Tuple.sort f) m) = m := by
  classical
  let σ := Tuple.sort f
  let g : Fin n → ℝ := f ∘ σ
  have hmono : Monotone g := Tuple.monotone_sort f
  have hginj : Function.Injective g := by
    intro a b h
    exact Equiv.injective σ (hinj h)
  have hgstrict : StrictMono g := by
    intro a b hab
    exact lt_of_le_of_ne (hmono hab.le) (fun h => hab.ne (hginj h))
  have hfilter :
      (Finset.univ.filter fun j => g j < g m) = Finset.Iio m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · intro hlt
      by_contra hnot
      have hmj : m ≤ j := le_of_not_gt hnot
      have hle : g m ≤ g j := hmono hmj
      exact not_lt_of_ge hle hlt
    · intro hjm
      exact hgstrict hjm
  have hperm :
      (Finset.univ.filter fun j => f j < f (σ m)) =
        (Finset.univ.filter fun j => g j < g m).map σ.toEmbedding := by
    ext j
    simp [g, σ]
  unfold lowerCount
  rw [hperm, Finset.card_map, hfilter, Fin.card_Iio]

lemma sorted_upper_count {n : ℕ} (f : Fin n → ℝ)
    (hinj : Function.Injective f) (m : Fin n) :
    upperCount f ((Tuple.sort f) m) = n - 1 - m := by
  classical
  let σ := Tuple.sort f
  let g : Fin n → ℝ := f ∘ σ
  have hmono : Monotone g := Tuple.monotone_sort f
  have hginj : Function.Injective g := by
    intro a b h
    exact Equiv.injective σ (hinj h)
  have hgstrict : StrictMono g := by
    intro a b hab
    exact lt_of_le_of_ne (hmono hab.le) (fun h => hab.ne (hginj h))
  have hfilter :
      (Finset.univ.filter fun j => g m < g j) = Finset.Ioi m := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    constructor
    · intro hlt
      by_contra hnot
      have hjm : j ≤ m := le_of_not_gt hnot
      have hle : g j ≤ g m := hmono hjm
      exact not_lt_of_ge hle hlt
    · intro hmj
      exact hgstrict hmj
  have hperm :
      (Finset.univ.filter fun j => f (σ m) < f j) =
        (Finset.univ.filter fun j => g m < g j).map σ.toEmbedding := by
    ext j
    simp [g, σ]
  unfold upperCount
  rw [hperm, Finset.card_map, hfilter, Fin.card_Ioi]

theorem median_index_exists {n : ℕ} (f : Fin n → ℝ)
    (hpos : 0 < n) (hinj : Function.Injective f) :
    ∃ i : Fin n, NearBalanced (lowerCount f i) (upperCount f i) := by
  classical
  let m : Fin n := ⟨n / 2, Nat.div_lt_self hpos (by decide : 1 < 2)⟩
  refine ⟨(Tuple.sort f) m, ?_⟩
  rw [sorted_lower_count f hinj m, sorted_upper_count f hinj m]
  exact nearBalanced_median_counts hpos

lemma physical_counts_eq_height_counts {n : ℕ} (pts : PointConfig n)
    (dir : Direction) (pivot : Fin n) :
    Line.physicalLeftCount pts (Direction.lineThrough dir (pts pivot)) pivot =
      upperCount (fun i => height dir (pts i)) pivot ∧
    Line.physicalRightCount pts (Direction.lineThrough dir (pts pivot)) pivot =
      lowerCount (fun i => height dir (pts i)) pivot := by
  classical
  constructor
  · unfold Line.physicalLeftCount Line.physicalLeftIndices upperCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact (isLeft_lineThrough_iff_height_lt dir (pts pivot) (pts i)).mp h.2
    · intro h
      refine ⟨?_, (isLeft_lineThrough_iff_height_lt dir (pts pivot) (pts i)).mpr h⟩
      intro hip
      subst i
      exact lt_irrefl _ h
  · unfold Line.physicalRightCount Line.physicalRightIndices lowerCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact (isRight_lineThrough_iff_height_lt dir (pts pivot) (pts i)).mp h.2
    · intro h
      refine ⟨?_, (isRight_lineThrough_iff_height_lt dir (pts pivot) (pts i)).mpr h⟩
      intro hip
      subst i
      exact lt_irrefl _ h

theorem balanced_start_exists {n : ℕ} (pts : PointConfig n)
    (hpos : 0 < n) (hgp : GeneralPosition pts) :
    ∃ pivot : Fin n, ∃ line : Line,
      Line.PhysicallyBalanced pts line pivot := by
  classical
  obtain ⟨dir, _hdir, hsep⟩ := exists_separating_direction pts hgp.distinct
  obtain ⟨pivot, hpivot⟩ :=
    median_index_exists (fun i => height dir (pts i)) hpos hsep
  refine ⟨pivot, Direction.lineThrough dir (pts pivot), ?_⟩
  constructor
  · exact Direction.lineThrough_contains dir (pts pivot)
  · have hcounts := physical_counts_eq_height_counts pts dir pivot
    rw [hcounts.1, hcounts.2]
    exact NearBalanced.symm hpivot

end Real
end Windmill
