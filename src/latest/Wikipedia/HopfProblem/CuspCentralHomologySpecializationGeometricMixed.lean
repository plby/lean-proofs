import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricThetaMarking
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricThetaCross
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricMixedCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricBoundary

/-!
# The geometric mixed specialization formula

The source class is the actual cross product of the literal weighted theta
edge cycle with a marked phase loop.  Its actual connecting class, its image
in the original base-period marking, and the winding numbers of the actual
edge characters identify its specialization with the previously oriented
fundamental classes of the three literal double curves.

The order is base before phase.  The middle theta edge is reversed, so the
three edge orientation signs are `(+1,-1,+1)`.  None of the target classes
or source coordinates is defined by this formula.
-/

noncomputable section

open scoped Matrix ContinuousMap ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricComponent CuspRetraction SpecializationModel FirstHurewicz
open SingularMayerVietoris PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin

/-- The literal weighted theta cycle crossed with the actual marked phase class,
then put into the phase--theta order used by the geometric boundary map. -/
def thetaMixedClass (β v : Fin 2 → ℤ) :
    SingularHomology (CompactFibreTorus × Theta) 2 :=
  singularHomologyMap (swapMap Theta CompactFibreTorus) 2
    (crossProductHomology Theta CompactFibreTorus 1
      (thetaEdgeHomology (thetaEdgeCycleCoefficients β) (thetaEdgeCycleCoefficients_sum β))
      (compactPhaseCoordinateHomology v))

/-- The connecting sign is the one obtained from the actual half-edge chains. -/
theorem thetaMixedClass_connecting (β v : Fin 2 → ℤ) :
    thetaConnecting (thetaMixedClass β v) =
      thetaBeltSum (fun j => thetaEdgeCycleCoefficients β j •
        compactPhaseCoordinateHomology v) :=
  thetaEdgeCross_connecting (thetaEdgeCycleCoefficients β)
    (thetaEdgeCycleCoefficients_sum β) (compactPhaseCoordinateHomology v)

/-- Actual cross-product naturality through the theta inclusion, with the
actual swaps retained on both sides. -/
theorem thetaProductMap_swappedCross
    (a : SingularHomology Theta 1) (b : SingularHomology CompactFibreTorus 1) :
    singularHomologyMap thetaProductMap 2
        (singularHomologyMap (swapMap Theta CompactFibreTorus) 2
          (crossProductHomology Theta CompactFibreTorus 1 a b)) =
      singularHomologyMap (swapMap (ProductTorus 2) CompactFibreTorus) 2
        (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
          (singularHomologyMap thetaBaseMap 1 a) b) := by
  have hcomp : thetaProductMap.comp (swapMap Theta CompactFibreTorus) =
      (swapMap (ProductTorus 2) CompactFibreTorus).comp
        (thetaBaseMap.prodMap (ContinuousMap.id CompactFibreTorus)) := by
    apply ContinuousMap.ext
    intro p
    rfl
  have hn := crossProductHomology_natural thetaBaseMap
    (ContinuousMap.id CompactFibreTorus) 1 a b
  change singularHomologyMap
      (thetaBaseMap.prodMap (ContinuousMap.id CompactFibreTorus)) 2
      (crossProductHomology Theta CompactFibreTorus 1 a b) =
    crossProductHomology (ProductTorus 2) CompactFibreTorus 1
      (singularHomologyMap thetaBaseMap 1 a)
      (singularHomologyMap (ContinuousMap.id CompactFibreTorus) 1 b) at hn
  rw [singularHomologyMap_id, LinearMap.id_apply] at hn
  change ((singularHomologyMap thetaProductMap 2).comp
    (singularHomologyMap (swapMap Theta CompactFibreTorus) 2))
      (crossProductHomology Theta CompactFibreTorus 1 a b) = _
  rw [← singularHomologyMap_comp, hcomp, singularHomologyMap_comp,
    LinearMap.comp_apply, hn]

/-- The theta construction gives the original marked base loop, without
replacing the base marking by a chosen isomorphism. -/
theorem thetaProductMap_thetaMixedClass (β v : Fin 2 → ℤ) :
    singularHomologyMap thetaProductMap 2 (thetaMixedClass β v) =
      singularHomologyMap (swapMap (ProductTorus 2) CompactFibreTorus) 2
        (crossProductHomology (ProductTorus 2) CompactFibreTorus 1
          (loopHomologyClass (coordinatePeriodLoop 2 β)) (compactPhaseCoordinateHomology v)) := by
  rw [thetaMixedClass, thetaProductMap_swappedCross, thetaBaseMap_thetaEdgeCoefficients]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The actual mixed specialization class, in the genuine named double curves. -/
theorem markedCollapse_mixed_doubleCurves (β v : Fin 2 → ℤ) :
    singularHomologyMap (markedCollapse C r hr) 2
        (coordinateTorusWedgeTwo
          (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]])) =
      ∑ j : Fin 3, (thetaEdgeCycleCoefficients β j *
        (hexagonRay (thetaEdgeIndex j) 0 * v 1 -
          hexagonRay (thetaEdgeIndex j) 1 * v 0)) •
        centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  rw [markedCollapse_mixedCoordinates, ← thetaProductMap_thetaMixedClass]
  exact productCollapse_thetaProductMap_of_coordinate_connecting
    C r hr hr1 hC hR (thetaMixedClass β v) (thetaEdgeCycleCoefficients β) v
    (thetaMixedClass_connecting β v)

/-- The two factors are the actual base and phase determinants with the
actual ray.  The sign is the explicitly proved orientation of its theta edge. -/
theorem markedCollapse_mixed_doubleCurves_det (β v : Fin 2 → ℤ) :
    singularHomologyMap (markedCollapse C r hr) 2
        (coordinateTorusWedgeTwo
          (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]])) =
      ∑ j : Fin 3, (thetaEdgeOrientationSign j *
        (hexagonRay (thetaEdgeIndex j) 0 * cuspVector β 1 -
          hexagonRay (thetaEdgeIndex j) 1 * cuspVector β 0) *
        (hexagonRay (thetaEdgeIndex j) 0 * v 1 -
          hexagonRay (thetaEdgeIndex j) 1 * v 0)) •
        centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  rw [markedCollapse_mixed_doubleCurves C r hr hr1 hC hR β v]
  simp only [thetaEdgeCycleCoefficients_det]

end Wikipedia.HopfProblem.CuspCentralHomology
