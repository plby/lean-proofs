import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupHomeomorph
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldChosenBase
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorSourceOrdersLocal

/-!
# The actual elliptic chart in the normalized punctured plane

Invert the genuine elliptic quotient chart and apply the constructed
normalized plane uniformization. The resulting complex function is an
analytic local biholomorphism on the whole unit disc. Its center is zero
or one, and its values agree exactly with the actual compact-base inverse
chart and with the actual regular-plane homeomorphism.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Triangle

attribute [local instance] triangleOrbitChartedSpace triangleRegularQuotientChartedSpace
  triangleCompactifiedChartedSpace

/-- The inverse original elliptic coordinate followed by the genuine
normalized uniformization of the full orbit curve. -/
def attachingPlanePartial (j : Kind) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω :=
  (triangleOrbitCoordinatePartial (.inr j)).symm.trans
    trianglePlaneUniformization.toPartialDiffeomorph

@[simp] theorem attachingPlanePartial_source (j : Kind) :
    (attachingPlanePartial j).source = (unitDisc : Set ℂ) := by
  change (ellipticFullChart j).target ∩
    (ellipticFullChart j).symm ⁻¹' (univ : Set TriangleOrbitSpace) = _
  rw [preimage_univ, inter_univ, ellipticFullChart_target]

/-- A fixed, actual complex function; outside the original chart target
it retains the chart's total inverse function. -/
def attachingPlaneCoordinate (j : Kind) : ℂ → ℂ := attachingPlanePartial j

@[simp] theorem attachingPlaneCoordinate_apply (j : Kind) (q : ℂ) :
    attachingPlaneCoordinate j q =
      trianglePlaneUniformization ((ellipticFullChart j).symm q) := rfl

theorem attachingPlaneCoordinate_isLocalDiffeomorphAt (j : Kind) {q : ℂ}
    (hq : q ∈ unitDisc) :
    IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω (attachingPlaneCoordinate j) q := by
  apply (attachingPlanePartial j).isLocalDiffeomorphAt _ _ _
  rwa [attachingPlanePartial_source]

theorem attachingPlaneCoordinate_analyticAt (j : Kind) {q : ℂ}
    (hq : q ∈ unitDisc) : AnalyticAt ℂ (attachingPlaneCoordinate j) q :=
  (attachingPlaneCoordinate_isLocalDiffeomorphAt j hq).contMDiffAt.contDiffAt.analyticAt

theorem attachingPlaneCoordinate_deriv_ne_zero (j : Kind) {q : ℂ}
    (hq : q ∈ unitDisc) : deriv (attachingPlaneCoordinate j) q ≠ 0 :=
  MuTorsor.SourceOrders.deriv_ne_zero_of_isLocalDiffeomorph
    (attachingPlaneCoordinate_isLocalDiffeomorphAt j hq)

theorem attachingPlaneCoordinate_analyticAt_zero (j : Kind) :
    AnalyticAt ℂ (attachingPlaneCoordinate j) 0 :=
  attachingPlaneCoordinate_analyticAt j (by simp [unitDisc])

theorem attachingPlaneCoordinate_deriv_zero_ne_zero (j : Kind) :
    deriv (attachingPlaneCoordinate j) 0 ≠ 0 :=
  attachingPlaneCoordinate_deriv_ne_zero j (by simp [unitDisc])

@[simp] theorem attachingPlaneCoordinate_zero (j : Kind) :
    attachingPlaneCoordinate j 0 = trianglePlaneUniformization (ellipticOrbitCenter j) := by
  rw [attachingPlaneCoordinate_apply, ← ellipticFullChart_center j]
  rw [(ellipticFullChart j).left_inv (ellipticFullChart_center_mem_source j)]

@[simp] theorem attachingPlaneCoordinate_three_zero :
    attachingPlaneCoordinate .three 0 = 0 := by
  rw [attachingPlaneCoordinate_zero, ellipticOrbitCenter_three,
    trianglePlaneUniformization_centerOne]

@[simp] theorem attachingPlaneCoordinate_four_zero :
    attachingPlaneCoordinate .four 0 = 1 := by
  rw [attachingPlaneCoordinate_zero, ellipticOrbitCenter_four,
    trianglePlaneUniformization_centerTwo]

/-- The actual compactified chart inverse is literally the original
orbit-chart inverse followed by the original open inclusion. -/
theorem attaching_compactInverse_eq (j : Kind) (q : ℂ) :
    (punctureChart (some j)).symm q =
      triangleOpenInclusion ((ellipticFullChart j).symm q) := rfl

/-- Agreement with the actual sphere uniformization holds for the fixed
total functions, hence in particular on every selected attaching circle. -/
theorem attachingPlaneCoordinate_compactInverse (j : Kind) (q : ℂ) :
    triangleSphereUniformization ((punctureChart (some j)).symm q) =
      ((attachingPlaneCoordinate j q : ℂ) : RiemannSphere) := by
  rw [attaching_compactInverse_eq, triangleSphereUniformization_openInclusion]
  rfl

/-- Any actual regular-quotient point with this inverse-chart image has
precisely the fixed plane-coordinate value. -/
theorem attachingPlaneCoordinate_eq_regularPlane (j : Kind) (q : ℂ)
    (x : TriangleRegularQuotient)
    (hx : regularInclusion x = (punctureChart (some j)).symm q) :
    (triangleRegularPlaneHomeomorph x : ℂ) = attachingPlaneCoordinate j q := by
  apply OnePoint.coe_injective (X := ℂ)
  calc
    ((triangleRegularPlaneHomeomorph x : ℂ) : RiemannSphere) =
        triangleSphereUniformization (regularInclusion x) := rfl
    _ = triangleSphereUniformization ((punctureChart (some j)).symm q) :=
      congrArg triangleSphereUniformization hx
    _ = ((attachingPlaneCoordinate j q : ℂ) : RiemannSphere) :=
      attachingPlaneCoordinate_compactInverse j q

/-- The actual regular-base inverse of a nonzero point in the chosen
small elliptic coordinate disc. -/
def attachingRegularBase (j : Kind) (q : ℂ)
    (hq : q ∈ Metric.ball 0 (specialBaseCover.radius (some j))) (hzero : q ≠ 0) :
    TriangleRegularQuotient :=
  regularBiholomorph.symm
    ⟨(punctureChart (some j)).symm q,
      (specialBaseCover.inverse_mem_regular_iff (some j) hq).mpr hzero⟩

@[simp] theorem regularInclusion_attachingRegularBase (j : Kind) (q : ℂ)
    (hq : q ∈ Metric.ball 0 (specialBaseCover.radius (some j))) (hzero : q ≠ 0) :
    regularInclusion (attachingRegularBase j q hq hzero) =
      (punctureChart (some j)).symm q :=
  regularBiholomorph_symm_coe _

/-- Exact agreement on every nonzero point of the actual chosen small
disc, with no choice of a replacement regular-base map. -/
@[simp] theorem triangleRegularPlaneHomeomorph_attachingRegularBase (j : Kind) (q : ℂ)
    (hq : q ∈ Metric.ball 0 (specialBaseCover.radius (some j))) (hzero : q ≠ 0) :
    (triangleRegularPlaneHomeomorph (attachingRegularBase j q hq hzero) : ℂ) =
      attachingPlaneCoordinate j q :=
  attachingPlaneCoordinate_eq_regularPlane j q _
    (regularInclusion_attachingRegularBase j q hq hzero)

theorem attachingPlaneCoordinate_mem_twicePuncturedPlane (j : Kind) {q : ℂ}
    (hq : q ∈ Metric.ball 0 (specialBaseCover.radius (some j))) (hzero : q ≠ 0) :
    attachingPlaneCoordinate j q ∈ twicePuncturedPlaneDomain := by
  rw [← triangleRegularPlaneHomeomorph_attachingRegularBase j q hq hzero]
  exact (triangleRegularPlaneHomeomorph (attachingRegularBase j q hq hzero)).property

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
