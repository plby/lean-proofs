import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCanonicalFrames

/-!
# The whole-real canonical boundary lift projects to the literal circle

The actual compatible meridian and the outer radial circle agree on the
entire unit interval. Their periodic extensions therefore agree at every
real time. Applying the exact boundary phase gives the literal positive
circle used by the slit cover, so its proved upper- and lower-slit bounds
apply to the actual covering lift without a new geometric hypothesis.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping Meridians Homology
open BoundaryRadius BoundaryCircleSlits BoundaryLoopSquares

/-- The unshifted actual radius-angle curve is one-periodic for every permitted radius. -/
theorem canonicalRadialCoordinate_periodic (b : Bool) (r : SmallRadius) :
    Function.Periodic (fun t : ℝ => radialCoordinate b (r, t)) 1 := by
  intro t
  have h := shiftedCircle_add_one b r (t - circlePhase b)
  simpa only [shiftedCircle_radialCoordinate,
    show t - circlePhase b + 1 + circlePhase b = t + 1 by ring, sub_add_cancel] using h

/-- The proved orientation makes the actual outer radial path the compatible meridian. -/
theorem canonicalRadialOuter_unit (b : Bool) (t : unitInterval) :
    radialCoordinate b (outerRadius, (t : ℝ)) = compatiblePlanarMeridian b t := by
  rw [radialCoordinate_outer_positiveMeridian, compatiblePlanarMeridian_eq,
    if_neg (not_lt.mpr normalizationOrientation_nonpos)]
  cases b <;> rfl

/-- The actual positive lift projects to the literal outer radial curve at every real time. -/
theorem canonicalPositiveLift_coordinate (b : Bool) (t : ℝ) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (canonicalPositiveLift b t)) =
      radialCoordinate b (outerRadius, t) := by
  have hp : Function.Periodic (fun u : ℝ =>
      triangleRegularPlaneHomeomorph (triangleRegularProject (canonicalPositiveLift b u))) 1 := by
    intro u
    simp only [canonicalPositiveLift_projection, loopPeriodic_add_one]
  have hu (u : unitInterval) :
      triangleRegularPlaneHomeomorph
          (triangleRegularProject (canonicalPositiveLift b (u : ℝ))) =
        compatiblePlanarMeridian b u := by
    rw [canonicalPositiveLift_projection, loopPeriodic_unit, compatibleRegularMeridian_coordinate]
  have hpositive := loopPeriodic_unique (p := compatiblePlanarMeridian b)
    (fun u : ℝ => triangleRegularPlaneHomeomorph
      (triangleRegularProject (canonicalPositiveLift b u))) hp hu
  have hradial := loopPeriodic_unique (p := compatiblePlanarMeridian b)
    (fun u : ℝ => radialCoordinate b (outerRadius, u))
    (canonicalRadialCoordinate_periodic b outerRadius) (canonicalRadialOuter_unit b)
  exact (congrFun hpositive t).trans (congrFun hradial t).symm

/-- The actual phase-shifted covering lift projects to the whole literal boundary circle. -/
theorem canonicalPhasedLift_coordinate (b : Bool) (t : ℝ) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (canonicalPhasedLift b t)) =
      shiftedCircle b outerRadius t := by
  change triangleRegularPlaneHomeomorph
      (triangleRegularProject (canonicalPositiveLift b (t + circlePhase b))) =
    radialCoordinate b (outerRadius, t + circlePhase b)
  exact canonicalPositiveLift_coordinate b (t + circlePhase b)

/-- The actual projected circle lies in the upper slit throughout the open unit turn. -/
theorem canonicalPhasedLift_mem_upperSlit (b : Bool) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (canonicalPhasedLift b t)) ∈
      upperSlit := by
  rw [canonicalPhasedLift_coordinate]
  exact shiftedCircle_mem_upperSlit b outerRadius ht0 ht1

/-- The actual projected circle lies in the lower slit throughout the centered open turn. -/
theorem canonicalPhasedLift_mem_lowerSlit (b : Bool) {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) :
    triangleRegularPlaneHomeomorph (triangleRegularProject (canonicalPhasedLift b t)) ∈
      lowerSlit := by
  rw [canonicalPhasedLift_coordinate]
  exact shiftedCircle_mem_lowerSlit b outerRadius ht0 ht1

/-- The same upper-slit containment in the literal regular-base open subset. -/
theorem canonicalPhasedLift_mem_upperBase (b : Bool) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    triangleRegularProject (canonicalPhasedLift b t) ∈ upperBase := by
  rw [mem_regularOpen]
  exact canonicalPhasedLift_mem_upperSlit b ht0 ht1

/-- The same lower-slit containment in the literal regular-base open subset. -/
theorem canonicalPhasedLift_mem_lowerBase (b : Bool) {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) :
    triangleRegularProject (canonicalPhasedLift b t) ∈ lowerBase := by
  rw [mem_regularOpen]
  exact canonicalPhasedLift_mem_lowerSlit b ht0 ht1

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
