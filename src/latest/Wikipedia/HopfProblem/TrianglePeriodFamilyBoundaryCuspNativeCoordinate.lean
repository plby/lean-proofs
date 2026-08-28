import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspNative
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansCircleBasic

/-!
# The native cusp circle in the actual normalized finite coordinate

The constructed sphere uniformization and the original finite-plane
uniformization agree pointwise.  The reciprocal cusp germ therefore
identifies the whole original native boundary loop with the inverse of
the actual analytic small-circle path, with its orientation reversed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle SpecialPeriods.CuspFamily CuspUniformization
open ThreefoldOverlapMappingTorus.Cusp SpecialPeriods.EllipticAttachingMeridians

attribute [local instance] triangleCompactifiedChartedSpace triangleOrbitChartedSpace

/-- The finite coordinate of the actual chosen sphere map is the
original normalized plane coordinate on every orbit. -/
theorem finiteProjection_eq_plane (z : UpperHalfPlane) :
    BetaTorsor.finiteProjection triangleSphereUniformization z =
      trianglePlaneUniformizationHomeomorph (triangleOrbitProjection z) := by
  rw [BetaTorsor.finiteProjection, BetaTorsor.finiteOrbitCoordinate,
    triangleSphereUniformization_openInclusion, BetaTorsor.sphereFiniteCoordinate_coe]
  exact congrArg (fun e : TriangleOrbitSpace ≃ₜ ℂ => e (triangleOrbitProjection z))
    trianglePlaneUniformization_toHomeomorph

/-- In particular the actual regular-plane homeomorphism uses the same finite coordinate. -/
theorem regularCoordinate_eq_finiteProjection (z : TriangleRegularPoint) :
    (triangleRegularPlaneHomeomorph (triangleRegularProject z) : ℂ) =
      BetaTorsor.finiteProjection triangleSphereUniformization z.val := by
  rw [triangleRegularPlaneHomeomorph_project, finiteProjection_eq_plane]

/-- The reciprocal identity holds on every native logarithmic boundary point. -/
theorem reciprocalCoordinate_baseLift (h : Height specialData.radius) (t : ℝ) :
    reciprocalCoordinate (exponential (logPoint specialData.radius specialData.radius_pos t h)) =
      ((triangleRegularPlaneHomeomorph (triangleRegularProject (baseLift h t)) : ℂ))⁻¹ := by
  have hp : BetaTorsor.finiteProjection triangleSphereUniformization (baseLift h t).val ≠ 0 := by
    rw [← regularCoordinate_eq_finiteProjection]
    exact (triangleRegularPlaneHomeomorph (triangleRegularProject (baseLift h t))).property.1
  have he := MuTorsor.CuspCoordinates.t_cuspQ_eq_inv_finiteProjection_of_mem
    triangleSphereUniformization triangleSphereUniformization_cusp (baseLift h t).val
    (baseLift_mem_horodisc h t) hp
  rw [baseLift_cuspQ] at he
  rw [regularCoordinate_eq_finiteProjection]
  exact he

/-- Parameter reversal converts the clockwise unit path to the actual
positive logarithmic exponential, with its exact integer period retained. -/
theorem clockwiseUnit_symm_exponential (t : unitInterval) :
    clockwiseUnit (unitInterval.symm t) = exponential (((t : ℝ) : ℂ) - 1) := by
  unfold clockwiseUnit exponential
  rw [unitInterval.coe_symm_eq]
  congr 1
  push_cast
  ring

/-- Every point of the positive native circle has the exact reversed
clockwise analytic-circle parameter. -/
theorem parameter_positive (h : Height specialData.radius) (t : unitInterval) :
    exponential (logPoint specialData.radius specialData.radius_pos (t : ℝ) h) =
      parameter h * clockwiseUnit (unitInterval.symm t) := by
  rw [clockwiseUnit_symm_exponential, parameter, ← exponential_add]
  apply (exponential_eq_iff _ _).mpr
  refine ⟨1, ?_⟩
  change ((t : ℝ) : ℂ) + (h : ℝ) * Complex.I =
    ((0 : ℝ) : ℂ) + (h : ℝ) * Complex.I + (((t : ℝ) : ℂ) - 1) + ((1 : ℤ) : ℂ)
  push_cast
  ring

/-- The actual real-periodic base projection, as a continuous map. -/
def projectedCurve (h : Height specialData.radius) : C(ℝ, TriangleRegularQuotient) :=
  ⟨fun t => triangleRegularProject (baseLift h t),
    triangleRegularProject_covering.continuous.comp (baseLift h).continuous⟩

/-- The native positive boundary loop, with its original actual basepoint. -/
def nativeLoop (h : Height specialData.radius) :
    Path (projectedCurve h 0) (projectedCurve h 0) :=
  realCurveLoop (projectedCurve h) (baseLift_projection_periodic h)

/-- The full loop agrees pointwise with the inverse of the actual
reciprocal-germ circle; this is not inferred from a deck endpoint. -/
theorem nativeLoop_coordinate (h : Height specialData.radius) (t : unitInterval) :
    (triangleRegularPlaneHomeomorph (nativeLoop h t) : ℂ) =
      (reciprocalCoordinate (parameter h * clockwiseUnit (unitInterval.symm t)))⁻¹ := by
  change (triangleRegularPlaneHomeomorph (triangleRegularProject (baseLift h (t : ℝ))) : ℂ) = _
  rw [← parameter_positive, reciprocalCoordinate_baseLift, inv_inv]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
