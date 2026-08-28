import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSignSourceCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseBoundaryHomology

/-! # The four sign families have the same actual local boundary homology map -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris

def signDerivativeComparisonEquiv (x y : Bool) :
    ParameterSpace rotatedInput ≃L[ℝ] ParameterSpace rotatedInput :=
  (signCoordinateDerivativeEquiv x y).trans (signCoordinateDerivativeEquiv true true).symm

theorem signDerivativeComparisonEquiv_coe (x y : Bool) :
    (signDerivativeComparisonEquiv x y).toContinuousLinearMap =
      (signParameterComparison x y).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro p
  change (signCoordinateDerivativeEquiv true true).symm
    (signCoordinateDerivativeEquiv x y p) = signParameterComparison x y p
  apply (signCoordinateDerivativeEquiv true true).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, signCoordinateDerivativeEquiv_apply x y,
    signCoordinateDerivativeEquiv_apply true true]
  exact congrArg (fun A : ParameterSpace rotatedInput →L[ℝ] TargetSpace input ↦ A p)
    (signCoordinateMap_fderiv_eq_comp x y)

theorem signDerivativeComparisonEquiv_det (x y : Bool) :
    (signDerivativeComparisonEquiv x y).toLinearEquiv.toLinearMap.det = 1 := by
  change (signDerivativeComparisonEquiv x y).toContinuousLinearMap.det = 1
  rw [signDerivativeComparisonEquiv_coe]
  exact signParameterComparison_det x y

def signBoundary (x y : Bool) :
    LocalDegree.BoundaryData (signCoordinateMap x y) (signCoordinateDerivativeEquiv x y) Set.univ :=
  Classical.choice (LocalDegree.nonempty_boundaryData_of_contDiffAt
    (signCoordinateDerivativeEquiv x y) (hasFDerivAt_signCoordinateDerivativeEquiv x y)
    (signCoordinateMap_zero x y) Filter.univ_mem (contDiffAt_signCoordinateMap x y))

/-- Equality of the actual nonlinear local boundary maps on integral homology. -/
theorem signBoundary_homology_eq (x y : Bool) (k : ℕ) :
    singularHomologyMap (signBoundary x y).normalizedMap k =
      singularHomologyMap (signBoundary true true).normalizedMap k := by
  apply LocalBoundaryComparison.normalized_homology_eq (parameterBasis rotatedInput)
  change 0 < (signDerivativeComparisonEquiv x y).toLinearEquiv.toLinearMap.det
  rw [signDerivativeComparisonEquiv_det]
  norm_num

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
