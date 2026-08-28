import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryOrientation
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMeridianTransitions

/-!
# Actual slit-section values at the canonical meridian endpoints

The proved normalization sign selects the reflected semicircles in the
upper slit. Uniqueness of actual covering lifts gives their precise deck
frames. The half-time values below are values of the literal concatenated
meridian paths, rather than assigned endpoint labels.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping Meridians Homology

/-- The actual upper section at the left overlap point is in the inverse first frame. -/
theorem canonicalUpperLeft :
    upperLiftOnOverlap normalizedSlitBaseLift 0 meridianLeftOverlapPoint =
      triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint := by
  have hn : ¬ 0 < normalizationOrientation := not_lt.mpr normalizationOrientation_nonpos
  change upperLift normalizedSlitBaseLift
    ⟨triangleRegularProject normalizedRegularMeridianLeftPoint, _⟩ = _
  have hp (t : unitInterval) : triangleRegularProject (reflectedZeroHalfPath t) ∈ upperBase := by
    rw [mem_regularOpen, reflectedZeroHalfPath_coordinate, oppositeZeroPath, if_neg hn]
    exact upperZeroPath_mem_upperSlitPlane t
  apply upperLift_endpoint normalizedSlitBaseLift _ reflectedZeroHalfPath hp
  exact (triangleRegularProject_covering.map_smul _).symm

/-- The actual upper section at the right overlap point is in the positive second frame. -/
theorem canonicalUpperRight :
    upperLiftOnOverlap normalizedSlitBaseLift 2 meridianRightOverlapPoint =
      triangleGenerator₂ • normalizedRegularMeridianRightPoint := by
  have hn : ¬ 0 < normalizationOrientation := not_lt.mpr normalizationOrientation_nonpos
  change upperLift normalizedSlitBaseLift
    ⟨triangleRegularProject normalizedRegularMeridianRightPoint, _⟩ = _
  have hp (t : unitInterval) : triangleRegularProject (reflectedOneHalfPath t) ∈ upperBase := by
    rw [mem_regularOpen, reflectedOneHalfPath_coordinate, oppositeOnePath, if_neg hn]
    exact upperOnePath_mem_upperSlitPlane t
  apply upperLift_endpoint normalizedSlitBaseLift _ reflectedOneHalfPath hp
  exact (triangleRegularProject_covering.map_smul _).symm

/-- The actual midpoint of the parameter interval. -/
def canonicalHalfTime : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] theorem canonicalHalfTime_coe : (canonicalHalfTime : ℝ) = 1 / 2 := rfl

private theorem path_trans_canonicalHalfTime {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) : (p.trans q) canonicalHalfTime = b := by
  rw [Path.trans_apply, dif_pos (show (canonicalHalfTime : ℝ) ≤ 1 / 2 from le_rfl)]
  calc
    _ = p 1 := congrArg p (Subtype.ext (by norm_num [canonicalHalfTime]))
    _ = b := p.target

/-- The first positive meridian reaches the actual reflected-zero endpoint at half time. -/
theorem compatibleMeridianLift_false_half :
    compatibleMeridianLift false canonicalHalfTime =
      triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint :=
  path_trans_canonicalHalfTime reflectedZeroHalfPath
    (liftedZeroHalfPath.symm.map (continuous_const_smul triangleGenerator₁⁻¹))

/-- The second positive meridian reaches the actual one-half-path endpoint at half time. -/
theorem compatibleMeridianLift_true_half :
    compatibleMeridianLift true canonicalHalfTime = normalizedRegularMeridianRightPoint :=
  path_trans_canonicalHalfTime liftedOneHalfPath
    ((reflectedOneHalfPath.symm.map (continuous_const_smul triangleGenerator₂⁻¹)).cast
      (inv_smul_smul triangleGenerator₂ normalizedRegularMeridianRightPoint).symm rfl)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
