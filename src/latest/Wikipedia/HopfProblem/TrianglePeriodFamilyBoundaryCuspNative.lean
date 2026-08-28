import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspRegular
import Wikipedia.HopfProblem.SpecialPeriodsTriangleSourceCusp
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansLinearization
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedCurve

/-!
# The actual native cusp lift and its controlled reciprocal coordinate

The positive real boundary parameter is the original logarithmic base
coordinate.  Its actual triangle deck transformation is retained.  The
reciprocal of the normalized finite coordinate is an actual analytic germ
with nonzero derivative, so a concrete higher logarithmic height lies in
the proved analytic linearization disc without an extra smallness input.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle SpecialPeriods.CuspFamily CuspUniformization
open ThreefoldOverlapMappingTorus.Cusp SpecialPeriods.EllipticAttachingMeridians

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual reciprocal target coordinate in the original filled cusp chart. -/
def reciprocalCoordinate : ℂ → ℂ :=
  MuTorsor.CuspCoordinates.t triangleSphereUniformization

@[simp] theorem reciprocalCoordinate_zero : reciprocalCoordinate 0 = 0 :=
  MuTorsor.CuspCoordinates.t_zero triangleSphereUniformization triangleSphereUniformization_cusp

theorem reciprocalCoordinate_analytic : AnalyticAt ℂ reciprocalCoordinate 0 :=
  MuTorsor.CuspCoordinates.t_analyticAt_zero
    triangleSphereUniformization triangleSphereUniformization_cusp

theorem reciprocalCoordinate_derivative : deriv reciprocalCoordinate 0 ≠ 0 :=
  TriangleSource.reciprocalCusp_deriv_ne_zero
    triangleSphereUniformization triangleSphereUniformization_cusp

/-- Quantitative control supplied by the actual noncritical reciprocal germ. -/
def reciprocalControl : LinearizationControl reciprocalCoordinate :=
  analyticLinearizationControl reciprocalCoordinate_analytic reciprocalCoordinate_derivative

/-- A literal height satisfying both the original overlap bound and the
actual reciprocal-germ linearization bound. -/
def controlledHeight : Height specialData.radius :=
  ⟨max (heightThreshold specialData.radius) (heightThreshold reciprocalControl.radius) + 1,
    by
      change heightThreshold specialData.radius <
        max (heightThreshold specialData.radius) (heightThreshold reciprocalControl.radius) + 1
      exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)⟩

/-- The positive cusp-circle coefficient at any allowed logarithmic height. -/
def parameter (h : Height specialData.radius) : ℂ :=
  exponential (logPoint specialData.radius specialData.radius_pos 0 h)

theorem parameter_ne_zero (h : Height specialData.radius) : parameter h ≠ 0 :=
  exponential_ne_zero _

/-- The chosen height satisfies the actual analytic disc estimate. -/
theorem parameter_controlled : ‖parameter controlledHeight‖ < reciprocalControl.radius := by
  apply (mem_logBase reciprocalControl.radius _).mp
  rw [mem_logBase_iff_height reciprocalControl.radius reciprocalControl.radius_pos,
    logPoint_im]
  change heightThreshold reciprocalControl.radius <
    max (heightThreshold specialData.radius) (heightThreshold reciprocalControl.radius) + 1
  exact lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)

/-- The original positive real cusp lift, for every allowed height. -/
def baseLift (h : Height specialData.radius) : C(ℝ, TriangleRegularPoint) :=
  ⟨fun t => logBaseToRegular specialData.radius specialRadius_cap
    (logPoint specialData.radius specialData.radius_pos t h),
    (logBaseToRegular_holomorphic specialData.radius specialRadius_cap).continuous.comp
      ((logBaseHeightHomeomorph specialData.radius specialData.radius_pos).symm.continuous.comp
        (continuous_const.prodMk continuous_id))⟩

/-- All integer translates retain the actual inverse cusp-generator convention. -/
theorem baseLift_translate (h : Height specialData.radius) (k : ℤ) (t : ℝ) :
    baseLift h (t + k) = (triangleCuspGenerator ^ (-k)) • baseLift h t := by
  have he := logBaseToRegular_translate specialData.radius specialRadius_cap (-k)
    (logPoint specialData.radius specialData.radius_pos t h)
  rw [logPoint_translate] at he
  simpa only [baseLift, ContinuousMap.coe_mk, Int.cast_neg, sub_neg_eq_add] using he

/-- The literal base projection is one-periodic. -/
theorem baseLift_projection_periodic (h : Height specialData.radius) :
    Function.Periodic (fun t : ℝ => triangleRegularProject (baseLift h t)) 1 := by
  intro t
  have he := congrArg triangleRegularProject (baseLift_translate h 1 t)
  simpa only [Int.cast_one, triangleRegularProject_covering.map_smul] using he

/-- Every point remains in the actual controlled geometric cusp horodisc. -/
theorem baseLift_mem_horodisc (h : Height specialData.radius) (t : ℝ) :
    (baseLift h t : UpperHalfPlane) ∈ horodisc width :=
  logBaseToRegular_mem_horodisc specialData.radius specialRadius_cap _

/-- Its original source cusp coordinate is exactly the native exponential. -/
theorem baseLift_cuspQ (h : Height specialData.radius) (t : ℝ) :
    cuspQ (baseLift h t : UpperHalfPlane) =
      exponential (logPoint specialData.radius specialData.radius_pos t h) :=
  logBaseToRegular_cuspQ specialData.radius specialRadius_cap _

/-- The actual original cusp boundary map keeps this base and the
unchanged rank-four fibre coordinate, with no affine replacement. -/
theorem boundaryToRegularFamily_mk (t : ℝ) (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.boundaryToRegularFamily none
        (MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient (baseLift specialHeight t, x) :=
  ThreefoldOverlapMappingTorus.Cusp.boundaryToRegularFamily_cusp_mk t x

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
