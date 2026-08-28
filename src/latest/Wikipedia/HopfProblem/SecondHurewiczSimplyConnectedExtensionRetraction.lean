import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionProjection

/-!
# An explicit retraction of the simplex cylinder onto its bottom and side

Projection is along rays starting at height two over the barycenter.
The maximum defining the denominator says that the ray hits either the
bottom or one of the actual barycentric faces. It fixes both pointwise.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

theorem retracted_mem_bottomOrSide {n : ℕ} (u : unitInterval × Simplex n) :
    (retractedTime u, retractedSimplex u) ∈ bottomOrSide n := by
  rcases le_total (1 - ((n : ℝ) + 1) * minimumCoordinate u.2)
      (1 - (u.1 : ℝ) / 2) with h | h
  · have hd : cylinderDenominator u = 1 - (u.1 : ℝ) / 2 := max_eq_left h
    left
    apply Subtype.ext
    change ((u.1 : ℝ) + 2 * cylinderDenominator u - 2) / cylinderDenominator u = 0
    have hn : (u.1 : ℝ) + 2 * cylinderDenominator u - 2 = 0 := by rw [hd]; ring
    rw [hn, zero_div]
  · have hd : cylinderDenominator u = 1 - ((n : ℝ) + 1) * minimumCoordinate u.2 :=
      max_eq_right h
    right
    obtain ⟨i, hi⟩ := exists_coordinate_eq_minimum u.2
    refine ⟨i, ?_⟩
    change (u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n) /
      cylinderDenominator u = 0
    have hn : u.2 i + (cylinderDenominator u - 1) * barycenterCoordinate n = 0 := by
      rw [hi, hd]
      calc
        _ = minimumCoordinate u.2 - minimumCoordinate u.2 *
            (((n : ℝ) + 1) * barycenterCoordinate n) := by ring
        _ = 0 := by rw [card_mul_barycenterCoordinate]; ring
    rw [hn, zero_div]

/-- The actual continuous radial retraction onto the bottom and side. -/
def cylinderRetraction (n : ℕ) : C(unitInterval × Simplex n, ↥(bottomOrSide n)) where
  toFun u := ⟨(retractedTime u, retractedSimplex u), retracted_mem_bottomOrSide u⟩
  continuous_toFun :=
    ((continuous_retractedTime n).prodMk (continuous_retractedSimplex n)).subtype_mk _

/-- The inclusion of the prescribed subspace into the whole cylinder. -/
def bottomOrSideInclusion (n : ℕ) : C(↥(bottomOrSide n), unitInterval × Simplex n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem cylinderRetraction_val_of_mem {n : ℕ} {u : unitInterval × Simplex n}
    (hu : u ∈ bottomOrSide n) : (cylinderRetraction n u).val = u :=
  Prod.ext (retractedTime_eq_of_mem hu) (retractedSimplex_eq_of_mem hu)

@[simp] theorem cylinderRetraction_fix {n : ℕ} (u : ↥(bottomOrSide n)) :
    cylinderRetraction n u.val = u :=
  Subtype.ext (cylinderRetraction_val_of_mem u.property)

@[simp] theorem cylinderRetraction_bottom (n : ℕ) (s : Simplex n) :
    cylinderRetraction n (0, s) = bottomInclusion n s :=
  cylinderRetraction_fix (bottomInclusion n s)

@[simp] theorem cylinderRetraction_side (n : ℕ) (t : unitInterval) (s : SimplexBoundary n) :
    cylinderRetraction n (t, s.val) = sideInclusion n (t, s) :=
  cylinderRetraction_fix (sideInclusion n (t, s))

/-- The displayed map is a retraction, not merely a map into the subspace. -/
theorem cylinderRetraction_retract (n : ℕ) :
    (cylinderRetraction n).comp (bottomOrSideInclusion n) =
      ContinuousMap.id (↥(bottomOrSide n)) := by
  apply ContinuousMap.ext
  intro u
  exact cylinderRetraction_fix u

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
