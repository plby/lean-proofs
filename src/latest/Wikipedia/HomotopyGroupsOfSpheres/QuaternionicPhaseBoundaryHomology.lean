import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseOrientation
import Wikipedia.HomotopyGroupsOfSpheres.PositiveBoundaryComparison

/-!
# Equal local boundary homology maps throughout the scalar phase family

Small boundaries are constructed from the derivatives of the actual
source-and-target coordinate maps. Their normalized maps induce the same
homology map as at phase zero, including in the relevant sixth degree.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris

def parameterBasis (z : UnitSphere) : Module.Basis (Fin 7) ℝ (ParameterSpace z) :=
  (Module.finBasis ℝ (ParameterSpace z)).reindex (finCongr (parameterSpace_finrank z))

theorem hasFDerivAt_phaseDerivativeEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) : HasFDerivAt (phaseCoordinates z a)
      (phaseDerivativeEquiv z hz a).toContinuousLinearMap 0 :=
  ((contDiffAt_phaseCoordinates z hz a (n := 1)).differentiableAt (by decide)).hasFDerivAt

def phaseBoundary (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) :
    LocalDegree.BoundaryData (phaseCoordinates z a) (phaseDerivativeEquiv z hz a) Set.univ :=
  Classical.choice (LocalDegree.nonempty_boundaryData_of_contDiffAt
    (phaseDerivativeEquiv z hz a) (hasFDerivAt_phaseDerivativeEquiv z hz a)
    (phaseCoordinates_zero z hz a) (Filter.univ_mem) (contDiffAt_phaseCoordinates z hz a))

/-- The actual small-boundary homology map is unchanged as the scalar phase varies. -/
theorem phaseBoundary_homology_eq (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (a : ℝ) (k : ℕ) :
    singularHomologyMap (phaseBoundary z hz a).normalizedMap k =
      singularHomologyMap (phaseBoundary z hz 0).normalizedMap k := by
  apply LocalBoundaryComparison.normalized_homology_eq (parameterBasis z)
  change 0 < (phaseDerivativeComparisonEquiv z hz a).toContinuousLinearMap.det
  rw [phaseDerivativeComparisonEquiv_coe]
  exact phaseDerivativeComparison_det_pos z hz a

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
