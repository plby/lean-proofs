import StackExchange.Puzzling139335.CornerMass.Placements

/-!
# Positive real weights for actual intrinsic corner types

These weights are constructed from the finite local masses of the actual
Jordan pieces. They are not an extra angle or incidence hypothesis. Their
sum is the same at every physical corner of the square.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335.SquareDissection

noncomputable section

open Classical in
theorem cornerTypeMassSum_toReal (d : SquareDissection) (j : Fin 4) (r : ℝ) :
    (d.cornerTypeMassSum j r).toReal =
      ∑ i, if corner j ∈ d.piece i then
        (localMass (d.piece 0) (d.intrinsicCorner i j) r).toReal else 0 := by
  classical
  have hfinite : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      (if corner j ∈ d.piece i then
        localMass (d.piece 0) (d.intrinsicCorner i j) r else 0) ≠ ∞ := by
    intro i _
    split_ifs
    · exact (localMass_lt_top _ _ _).ne
    · exact ENNReal.zero_ne_top
  unfold cornerTypeMassSum
  rw [ENNReal.toReal_sum hfinite]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

open Classical in
/-- Every intrinsic type occurring at a square corner has a strictly
positive real weight, with equal total weight at all four square corners.
The weights are the actual local weighted areas at one common radius. -/
theorem exists_positive_cornerType_weights (d : SquareDissection) :
    ∃ m : Plane → ℝ,
      (∀ v ∈ d.usedCornerTypes, 0 < m v) ∧
      ∀ j k : Fin 4,
        (∑ i, if corner j ∈ d.piece i then m (d.intrinsicCorner i j) else 0) =
          ∑ i, if corner k ∈ d.piece i then m (d.intrinsicCorner i k) else 0 := by
  classical
  obtain ⟨m, hm, hcorners⟩ := d.exists_positive_corner_weights_of_placements
    (d.piece 0) (d.jordan 0) d.placement d.placement_image
  refine ⟨m, ?_, ?_⟩
  · intro v hv
    exact hm v (d.usedCornerTypes_subset hv)
  · intro j k
    exact hcorners j k

end

end Puzzling139335.SquareDissection
