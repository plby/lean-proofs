import Wikipedia.NoExoticSixSphere.QuaternionCommutatorTangentEquiv
import Wikipedia.NoExoticSixSphere.SphereCenteredChartDifferential
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Local regularity of the actual quaternion commutator projection

The source and target maps are actual centered sphere charts. Their
coordinate expression has the proved invertible derivative, so the
inverse function theorem gives a genuine local homeomorphism at the
unique antipodal preimage. A global degree calculation is not asserted.
-/

noncomputable section

open scoped ContDiff commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorLocalRegularity

open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration SphereCenteredCoordinates
open QuaternionCommutatorRotation QuaternionCommutatorSourceChart
open QuaternionCommutatorAntipodal QuaternionCommutatorTangentEquiv

theorem projectionMap_zero : QuaternionCommutatorSourceChart.projectionMap 0 = antipode := by
  apply (projection_eq_antipode_iff _).mpr
  change (⁅fiberInclusion (quaternionChart 0),
    conjugatedFiber (Real.pi / 4 + 0) (quaternionChart 0)⁆).val 0 0 = -1
  rw [add_zero]
  exact commutator_top_of_neg_and_unit _ _ quaternionChart_zero
    (midpoint_offDiagonal_norm _ quaternionChart_zero)

def coordinateMap (z : Parameters) : TargetTangent :=
  stereoToFun (-antipode.val) (QuaternionCommutatorSourceChart.projectionMap z).val

theorem coordinateMap_eq_chart (z : Parameters) :
    coordinateMap z = chart antipode (QuaternionCommutatorSourceChart.projectionMap z) := rfl

theorem coordinateMap_zero : coordinateMap 0 = 0 := by
  rw [coordinateMap_eq_chart, projectionMap_zero, chart_self]

theorem hasFDerivAt_coordinateMap : HasFDerivAt coordinateMap tangentDerivative 0 := by
  have hc : HasFDerivAt (stereoToFun (-antipode.val)) TargetTangent.orthogonalProjectionOnto
      (QuaternionCommutatorSourceChart.projectionMap 0).val := by
    rw [projectionMap_zero]
    exact SphereCenteredChartDifferential.hasFDerivAt_chart antipode
  have h := hc.comp 0 hasFDerivAt_projectionMap
  change HasFDerivAt coordinateMap
    (TargetTangent.orthogonalProjectionOnto.comp ambientDerivative) 0 at h
  rwa [← tangentDerivative_eq_projection] at h

theorem contDiffAt_coordinateMap : ContDiffAt ℝ 1 coordinateMap 0 := by
  have hc : ContDiffAt ℝ 1 (stereoToFun (-antipode.val))
      (QuaternionCommutatorSourceChart.projectionMap 0).val := by
    rw [projectionMap_zero]
    exact contDiffAt_stereoToFun antipode
  exact hc.comp 0 contDiff_projectionMap.contDiffAt

theorem hasStrictFDerivAt_coordinateMap :
    HasStrictFDerivAt coordinateMap tangentEquiv.toContinuousLinearMap 0 :=
  contDiffAt_coordinateMap.hasStrictFDerivAt' hasFDerivAt_coordinateMap (by decide)

def localHomeomorph : OpenPartialHomeomorph Parameters TargetTangent :=
  hasStrictFDerivAt_coordinateMap.toOpenPartialHomeomorph coordinateMap

theorem localHomeomorph_apply (z : Parameters) : localHomeomorph z = coordinateMap z := rfl

theorem zero_mem_localHomeomorph_source : (0 : Parameters) ∈ localHomeomorph.source :=
  hasStrictFDerivAt_coordinateMap.mem_toOpenPartialHomeomorph_source

theorem zero_mem_localHomeomorph_target : (0 : TargetTangent) ∈ localHomeomorph.target := by
  have h := hasStrictFDerivAt_coordinateMap.image_mem_toOpenPartialHomeomorph_target
  change coordinateMap 0 ∈ localHomeomorph.target at h
  rwa [coordinateMap_zero] at h

end NoExoticSixSphere.QuaternionCommutatorLocalRegularity
