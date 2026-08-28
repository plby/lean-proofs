import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalForms
import Wikipedia.HopfProblem.SpecialPeriodsTriangleSourceCusp

/-!
# The literal reciprocal sphere coordinate along the actual cusp fibre

The coordinate used by the cusp filling is related to the standard
reciprocal coordinate by an actual analytic unit.  The identity is proved
on the full glued cusp patch using the original chart inverse, including
on the central fibre.  In particular the standard sphere coordinate does
not silently replace the toric parameter.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCusp

open Triangle MuTorsor.CuspCoordinates

attribute [local instance] triangleCompactifiedChartedSpace Threefold.chartedSpace
  CuspGeometry.nativeChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The unchanged reciprocal chart of the fixed standard sphere atlas. -/
abbrev reciprocalCoordinate : RiemannSphere → ℂ := sphereReciprocalCoordinate

/-- The actual transition from the filling's exponential parameter. -/
def coordinateChange : ℂ → ℂ := t triangleSphereUniformization

/-- Its actual divided difference, not an assumed transition unit. -/
def coordinateUnit : ℂ → ℂ := tDivQ triangleSphereUniformization

@[simp] theorem reciprocalCoordinate_infty :
    reciprocalCoordinate (∞ : RiemannSphere) = 0 := sphereReciprocalCoordinate_infty

theorem reciprocalCoordinate_coe {z : ℂ} (hz : z ≠ 0) :
    reciprocalCoordinate (z : RiemannSphere) = z⁻¹ := sphereReciprocalCoordinate_coe hz

@[simp] theorem coordinateChange_zero : coordinateChange 0 = 0 :=
  t_zero triangleSphereUniformization triangleSphereUniformization_cusp

theorem coordinateChange_analyticAt : AnalyticAt ℂ coordinateChange 0 :=
  t_analyticAt_zero triangleSphereUniformization triangleSphereUniformization_cusp

theorem coordinateChange_deriv_ne_zero : deriv coordinateChange 0 ≠ 0 :=
  TriangleSource.reciprocalCusp_deriv_ne_zero triangleSphereUniformization
    triangleSphereUniformization_cusp

theorem coordinateUnit_analyticAt : AnalyticAt ℂ coordinateUnit 0 :=
  tDivQ_analyticAt_zero triangleSphereUniformization triangleSphereUniformization_cusp

theorem coordinateUnit_zero_ne_zero : coordinateUnit 0 ≠ 0 :=
  TriangleSource.reciprocalCusp_tDivQ_zero_ne_zero triangleSphereUniformization
    triangleSphereUniformization_cusp

theorem coordinateChange_eq_mul_unit (q : ℂ) :
    coordinateChange q = q * coordinateUnit q :=
  t_eq_mul_tDivQ triangleSphereUniformization triangleSphereUniformization_cusp q

/-- The equality is for the actual projection of every point of the
original cusp quotient, not only for a germ on the base. -/
theorem reciprocal_projection_inclusion (x : CuspGeometry.LocalSpace) :
    reciprocalCoordinate (Threefold.projectionSphere (CuspGeometry.inclusion x)) =
      coordinateChange (CuspGeometry.parameter x) := by
  have hleft : (cuspFullChart width le_rfl).symm (CuspGeometry.parameter x) =
      Threefold.projection (CuspGeometry.inclusion x) := by
    rw [← CuspGeometry.cuspCoordinate_inclusion x]
    exact (cuspFullChart width le_rfl).left_inv
      (CuspGeometry.projection_inclusion_mem_chart x)
  change sphereReciprocalCoordinate
      (triangleSphereUniformization (Threefold.projection (CuspGeometry.inclusion x))) =
    sphereReciprocalCoordinate
      (triangleSphereUniformization ((cuspFullChart width le_rfl).symm
        (CuspGeometry.parameter x)))
  rw [hleft]

theorem reciprocal_projection_inclusion_eq_mul_unit (x : CuspGeometry.LocalSpace) :
    reciprocalCoordinate (Threefold.projectionSphere (CuspGeometry.inclusion x)) =
      CuspGeometry.parameter x * coordinateUnit (CuspGeometry.parameter x) := by
  rw [reciprocal_projection_inclusion, coordinateChange_eq_mul_unit]

/-- The literal standard reciprocal coordinate equals the actual toric
parameter times its proved analytic unit throughout the full cusp patch. -/
theorem reciprocal_projection_eq_mul_unit {y : Threefold.Space}
    (hy : y ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space)) :
    reciprocalCoordinate (Threefold.projectionSphere y) =
      CuspGeometry.cuspCoordinate y * coordinateUnit (CuspGeometry.cuspCoordinate y) := by
  let x := CuspGeometry.nativePatchBiholomorph.symm ⟨y, hy⟩
  have hx : CuspGeometry.inclusion x = y :=
    congrArg Subtype.val (CuspGeometry.nativePatchBiholomorph.apply_symm_apply ⟨y, hy⟩)
  rw [← hx, CuspGeometry.cuspCoordinate_inclusion]
  exact reciprocal_projection_inclusion_eq_mul_unit x

/-- The divisor equation in every genuine cusp normal-crossing chart
uses the same standard reciprocal coordinate, with each branch appearing
once and with the actual base-coordinate unit. -/
theorem reciprocal_normalCrossingChart (x : CuspGeometry.LocalSpace)
    (hx : CuspGeometry.parameter x = 0) :
    ∃ J : Finset (Fin 3),
      ∃ e : PartialDiffeomorph IF (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
          Threefold.Space (ToricCharts.CoordinateSpace 3) ω,
      J.card = CuspQuotient.branchCount CuspGeometry.data.correction
        CuspGeometry.data.radius x ∧ J.Nonempty ∧
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target,
        reciprocalCoordinate (Threefold.projectionSphere (e.symm w)) =
          (∏ j ∈ J, w j) * coordinateUnit (∏ j ∈ J, w j) := by
  obtain ⟨J, e, hcard, hJ, hxs, hzero, hsource, hprod⟩ :=
    CuspNormalForms.normalCrossingChart_with_branchCount x hx
  refine ⟨J, e, hcard, hJ, hxs, hzero, hsource, ?_⟩
  intro w hw
  exact (reciprocal_projection_eq_mul_unit (hsource (e.map_target hw))).trans
    (congrArg (fun q : ℂ => q * coordinateUnit q) (hprod w hw))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCusp
