import Wikipedia.HopfProblem.SpecialPeriodsThreefoldPieces
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapSphere

/-!
# The unconditional cusp overlap in the common threefold model

The actual normalized sphere equivalence and constructed global period
formula instantiate the native full cusp-to-regular partial biholomorphism.
Composing with the proved identity change of cusp coordinate model leaves
the underlying map unchanged.  Its full source and target are the precise
inverse images needed by the four-piece gluing.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle ToricCharts

attribute [local instance] triangleCompactifiedChartedSpace specialCuspPieceChartedSpace
  specialRegularFamilyChartedSpace

local instance : ChartedSpace (CoordinateSpace 3) SpecialCuspPiece :=
  CuspPiece.nativeChartedSpace specialCuspData specialBaseCover specialCuspRadius_le

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

/-- The actual native cusp overlap, with every source and period premise
discharged by the unconditional global constructions. -/
def specialCuspNativeOverlap :
    PartialDiffeomorph I₃ IF SpecialCuspPiece SpecialRegularFamily ω :=
  CuspGlobalOverlap.sphereCuspToRegularPartial triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le
    specialBaseCover_cusp_radius_bounds.2.2.le

theorem specialCuspNativeOverlap_source_iff (x : SpecialCuspPiece) :
    x ∈ specialCuspNativeOverlap.source ↔
      CuspQuotient.projection specialCuspData.correction (specialBaseCover.radius none) x ≠ 0 :=
  CuspGlobalOverlap.sphereCuspToRegularPartial_source_iff triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le
    specialBaseCover_cusp_radius_bounds.2.2.le x

theorem specialCuspNativeOverlap_target_iff (y : SpecialRegularFamily) :
    y ∈ specialCuspNativeOverlap.target ↔
      specialRegularFamilyProjectionToBase y ∈ (punctureChart none).source ∧
        ‖punctureChart none (specialRegularFamilyProjectionToBase y)‖ <
          specialBaseCover.radius none :=
  CuspGlobalOverlap.sphereCuspToRegularPartial_target_iff triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le
    specialBaseCover_cusp_radius_bounds.2.2.le y

theorem specialCuspNativeOverlap_base (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspNativeOverlap.source) :
    specialRegularFamilyProjectionToBase (specialCuspNativeOverlap x) =
      specialCuspPieceProjectionToBase x :=
  CuspGlobalOverlap.sphereCuspToRegularPartial_preserves_base triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le
    specialBaseCover_cusp_radius_bounds.2.2.le x
    ((specialCuspNativeOverlap_source_iff x).mp hx)

/-- The same actual map, now in the common threefold coordinate model. -/
def specialCuspOverlap : PartialDiffeomorph IF IF SpecialCuspPiece SpecialRegularFamily ω :=
  (Diffeomorph.toPartialDiffeomorph
    (CuspPiece.nativeToCommon specialCuspData specialBaseCover specialCuspRadius_le).symm).trans
      specialCuspNativeOverlap

@[simp] theorem specialCuspOverlap_apply (x : SpecialCuspPiece) :
    specialCuspOverlap x = specialCuspNativeOverlap x := rfl

/-- The source is the complete inverse image of the regular base patch. -/
theorem specialCuspOverlap_source :
    specialCuspOverlap.source = specialCuspPieceProjectionToBase ⁻¹'
      (regularPatch : Set TriangleCompactifiedOrbitSpace) := by
  ext x
  change (x ∈ (univ : Set SpecialCuspPiece) ∧ x ∈ specialCuspNativeOverlap.source) ↔ _
  simp only [mem_univ, true_and]
  exact (specialCuspNativeOverlap_source_iff x).trans
    (CuspPiece.projectionToBase_mem_regular_iff specialCuspData specialBaseCover x).symm

/-- The target is the entire regular-family inverse image of the chosen
actual cusp patch, not a smaller neighborhood of one section. -/
theorem specialCuspOverlap_target :
    specialCuspOverlap.target = specialRegularFamilyProjectionToBase ⁻¹'
      (specialBaseCover.fillingPatch none : Set TriangleCompactifiedOrbitSpace) := by
  ext y
  change (y ∈ specialCuspNativeOverlap.target ∧
    specialCuspNativeOverlap.symm y ∈ (univ : Set SpecialCuspPiece)) ↔ _
  simp only [mem_univ, and_true]
  exact (specialCuspNativeOverlap_target_iff y).trans
    (specialBaseCover.mem_fillingPatch none (specialRegularFamilyProjectionToBase y)).symm

theorem specialCuspOverlap_base (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspOverlap.source) :
    specialRegularFamilyProjectionToBase (specialCuspOverlap x) =
      specialCuspPieceProjectionToBase x :=
  specialCuspNativeOverlap_base x hx.2

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
