import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspOverlapCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspOverlap

/-!
# Equivariance of the actual cusp gluing overlap

The constructed cusp periods agree with the constructed global periods
on the original logarithmic cusp coordinate.  Consequently the original
full cusp-to-regular partial biholomorphism intertwines the two actual
vertical flows, in both directions and on its complete source and target.
All period and geometric premises are discharged by the special data.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp

open Wikipedia.HopfProblem.SpecialPeriods.Triangle (triangleSphereUniformization
  triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
  triangleSphereUniformization_centerTwo)

attribute [local instance] specialCuspPieceChartedSpace specialRegularFamilyChartedSpace

/-- The actual vertical cusp flow preserves the entire gluing source. -/
theorem specialFlow_mem_overlap_source_iff (s : ℂ) (x : SpecialCuspPiece) :
    specialFlow s x ∈ specialCuspOverlap.source ↔ x ∈ specialCuspOverlap.source := by
  simp only [specialCuspOverlap_source, mem_preimage,
    specialCuspPieceProjectionToBase_specialFlow]

/-- The actual regular flow preserves the entire cusp-overlap target. -/
theorem regularFlow_mem_overlap_target_iff (s : ℂ) (x : SpecialRegularFamily) :
    Regular.flow s x ∈ specialCuspOverlap.target ↔ x ∈ specialCuspOverlap.target := by
  simp only [specialCuspOverlap_target, mem_preimage, Regular.flow_projection]

/-- The unchanged cusp gluing map intertwines the actual vertical flows
at every point of its full source. -/
theorem specialCuspOverlap_specialFlow (s : ℂ) (x : SpecialCuspPiece)
    (hx : x ∈ specialCuspOverlap.source) :
    specialCuspOverlap (specialFlow s x) = Regular.flow s (specialCuspOverlap x) := by
  have hp := CuspGlobalOverlap.spherePeriod_agreement triangleSphereUniformization
    triangleSphereUniformization_cusp triangleSphereUniformization_centerOne
    triangleSphereUniformization_centerTwo (specialBaseCover.radius none)
    (specialBaseCover.radius_pos none) specialCuspRadius_le
    specialBaseCover_cusp_radius_bounds.2.2.le
  have hn := (specialCuspNativeOverlap_source_iff x).mp hx.2
  exact cuspToRegularPartial_flow CuspGeometry.data Regular.data
    specialBaseCover_cusp_radius_bounds.2.2.le hp s x hn

/-- The inverse of the original gluing map also intertwines the actions
on every point of its full target. -/
theorem specialCuspOverlap_symm_regularFlow (s : ℂ) (y : SpecialRegularFamily)
    (hy : y ∈ specialCuspOverlap.target) :
    specialCuspOverlap.symm (Regular.flow s y) = specialFlow s (specialCuspOverlap.symm y) := by
  have hx := specialCuspOverlap.map_target hy
  have hsx := (specialFlow_mem_overlap_source_iff s (specialCuspOverlap.symm y)).mpr hx
  have he := specialCuspOverlap_specialFlow s (specialCuspOverlap.symm y) hx
  have he' : specialCuspOverlap (specialFlow s (specialCuspOverlap.symm y)) =
      Regular.flow s y := he.trans (congrArg (Regular.flow s) (specialCuspOverlap.right_inv hy))
  calc
    specialCuspOverlap.symm (Regular.flow s y) =
        specialCuspOverlap.symm (specialCuspOverlap (specialFlow s (specialCuspOverlap.symm y))) :=
      congrArg specialCuspOverlap.symm he'.symm
    _ = specialFlow s (specialCuspOverlap.symm y) := specialCuspOverlap.left_inv hsx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Cusp
