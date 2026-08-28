import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricMixed
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationGeometricMixedBasis
import Wikipedia.HopfProblem.CuspCentralCohomologyDoubleCurvesSlopeIdentification

/-!
# The actual native pullbacks of the named double-curve duals

The actual mixed specialization formula is evaluated against the native
cohomology classes dual to the three previously oriented named double
curves.  Together with the proved pure-coordinate vanishings, these
evaluations identify the pullbacks with the displayed quadratic slope
classes.  The source marking is the original ordered period marking, and
the sign is determined by the literal theta paths and cylinder orientations.

For the actual ray `r_j`, its normal is `ν_j = (-r_j 1,r_j 0)`.  The
mixed evaluation is `σ_j ν_j(B₀β)ν_j(v)`, hence the native pulled-back
class is `-σ_j` times the displayed slope polynomial.  This statement
does not silently identify the actual ray enumeration with any differently
ordered illustrative list of normals.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace ToricComponent CuspRetraction CuspCentralHomology
open CuspCentralHomology.SpecializationModel
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- Evaluating the actual mixed specialization on the already fixed
geometric curve dual reads off its genuine edge-character coefficient. -/
theorem doubleCurveDualClass_pullback_evaluate_mixedWedge
    (j : Fin 3) (β v : Fin 2 → ℤ) :
    singularEvaluation (ProductTorus 4) 2
        (singularCohomologyPullback (markedCollapse C r hr) 2
          (doubleCurveDualClass C r hr hr1 hC hR j))
        (coordinateTorusWedgeTwo
          (exteriorPower.ιMulti ℤ 2 ![![β 0, β 1, 0, 0], ![0, 0, v 0, v 1]])) =
      thetaEdgeCycleCoefficients β j *
        (hexagonRay (thetaEdgeIndex j) 0 * v 1 -
          hexagonRay (thetaEdgeIndex j) 1 * v 0) := by
  rw [singularEvaluation_naturality,
    markedCollapse_mixed_doubleCurves C r hr hr1 hC hR β v]
  simp only [map_sum, map_zsmul, doubleCurveDualClass_evaluate_curve, zsmul_eq_mul]
  simp

/-- The same evaluation in the actual ordered-minor homology coordinates. -/
theorem doubleCurveDualClass_pullback_evaluate_mixedCoordinates
    (j : Fin 3) (β v : Fin 2 → ℤ) :
    singularEvaluation (ProductTorus 4) 2
        (singularCohomologyPullback (markedCollapse C r hr) 2
          (doubleCurveDualClass C r hr hr1 hC hR j))
        (coordinateTorusH2Coordinates.symm (mixedPeriodCoordinates β v)) =
      thetaEdgeCycleCoefficients β j *
        (hexagonRay (thetaEdgeIndex j) 0 * v 1 -
          hexagonRay (thetaEdgeIndex j) 1 * v 0) := by
  rw [← mixedWedge_eq_coordinates_symm]
  exact doubleCurveDualClass_pullback_evaluate_mixedWedge C r hr hr1 hC hR j β v

/-- The geometric formula uses the original integral matrix `B₀` and
the normal of the actual named curve's ray, with its computed orientation. -/
theorem doubleCurveDualClass_pullback_evaluate_mixedCoordinates_B₀
    (j : Fin 3) (β v : Fin 2 → ℤ) :
    singularEvaluation (ProductTorus 4) 2
        (singularCohomologyPullback (markedCollapse C r hr) 2
          (doubleCurveDualClass C r hr hr1 hC hR j))
        (coordinateTorusH2Coordinates.symm (mixedPeriodCoordinates β v)) =
      thetaEdgeOrientationSign j *
        (-hexagonRay (thetaEdgeIndex j) 1 * (B₀ *ᵥ β) 0 +
          hexagonRay (thetaEdgeIndex j) 0 * (B₀ *ᵥ β) 1) *
        (-hexagonRay (thetaEdgeIndex j) 1 * v 0 +
          hexagonRay (thetaEdgeIndex j) 0 * v 1) := by
  rw [doubleCurveDualClass_pullback_evaluate_mixedCoordinates C r hr hr1 hC hR j β v,
    thetaEdgeCycleCoefficients_det]
  have hB : B₀ *ᵥ β = cuspVector β := by
    funext i
    fin_cases i <;> simp [B₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two, cuspVector]
  rw [hB]
  ring

/-- The pullback of the native class dual to each literal named double
curve is exactly its signed quadratic slope class in the original marking. -/
theorem doubleCurveDualClass_pullback_eq_slopeClass (j : Fin 3) :
    singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j) =
      (-thetaEdgeOrientationSign j) •
        slopeClass (-hexagonRay (thetaEdgeIndex j) 1) (hexagonRay (thetaEdgeIndex j) 0) := by
  apply eq_neg_smul_slopeClass_of_mixed_evaluate _
    (-hexagonRay (thetaEdgeIndex j) 1) (hexagonRay (thetaEdgeIndex j) 0)
    (thetaEdgeOrientationSign j)
  · exact doubleCurveDualClass_pullback_coordinate_zero C r hr hr1 hC hR j
  · exact doubleCurveDualClass_pullback_coordinate_five C r hr hr1 hC hR j
  · exact doubleCurveDualClass_pullback_evaluate_mixedCoordinates_B₀ C r hr hr1 hC hR j

/-- All six native pullback coefficients, with no unproved source or
target marking compatibility hypothesis. -/
theorem doubleCurveDualClass_pullback_coordinates (j : Fin 3) :
    coordinateTorusH2CohomologyCoordinates
        (singularCohomologyPullback (markedCollapse C r hr) 2
          (doubleCurveDualClass C r hr hr1 hC hR j)) =
      (-thetaEdgeOrientationSign j) •
        slopeCoefficients (-hexagonRay (thetaEdgeIndex j) 1) (hexagonRay (thetaEdgeIndex j) 0) := by
  rw [doubleCurveDualClass_pullback_eq_slopeClass C r hr hr1 hC hR j,
    map_zsmul, slopeClass_coordinates]

/-- The source's displayed polynomial as an equality in actual native
singular cohomology, using the actual ray normal and curve orientation. -/
theorem doubleCurveDualClass_pullback_linearCombination (j : Fin 3) :
    singularCohomologyPullback (markedCollapse C r hr) 2
        (doubleCurveDualClass C r hr hr1 hC hR j) =
      (-thetaEdgeOrientationSign j) •
        ((hexagonRay (thetaEdgeIndex j) 0 ^ 2) • coordinateTorusH2DualClass 2 -
          ((-hexagonRay (thetaEdgeIndex j) 1) ^ 2) • coordinateTorusH2DualClass 3 +
          ((-hexagonRay (thetaEdgeIndex j) 1) * hexagonRay (thetaEdgeIndex j) 0) •
            (coordinateTorusH2DualClass 1 - coordinateTorusH2DualClass 4)) := by
  rw [doubleCurveDualClass_pullback_eq_slopeClass C r hr hr1 hC hR j,
    slopeClass_eq_linearCombination]

end Wikipedia.HopfProblem.CuspCentralCohomology
