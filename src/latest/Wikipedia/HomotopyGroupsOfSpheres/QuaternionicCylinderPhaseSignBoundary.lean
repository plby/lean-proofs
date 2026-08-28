import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseSignBoundary
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCylinderDerivative

/-! # The common phase/sign boundary map in smooth cylinder coordinates -/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris

attribute [local irreducible] phaseSignDerivativeEquiv cylinderAngularDerivativeEquiv

def cylinderPhaseSignCoordinates (x y : Bool) (a : ℝ) :
    ParameterSpace rotatedInput → TargetSpace input :=
  phaseSignCoordinates x y a ∘ cylinderAngularParameters rotatedInput

theorem cylinderPhaseSignCoordinates_zero (x y : Bool) (a : ℝ) :
    cylinderPhaseSignCoordinates x y a 0 = 0 := by
  simp only [cylinderPhaseSignCoordinates, Function.comp_apply,
    cylinderAngularParameters_zero, phaseSignCoordinates_zero]

theorem contDiffAt_cylinderPhaseSignCoordinates (x y : Bool) (a : ℝ) {n : ℕ∞ω} :
    ContDiffAt ℝ n (cylinderPhaseSignCoordinates x y a) 0 := by
  have h : ContDiffAt ℝ n (phaseSignCoordinates x y a)
      (cylinderAngularParameters rotatedInput 0) := by
    rw [cylinderAngularParameters_zero]
    exact contDiffAt_phaseSignCoordinates x y a
  exact h.comp 0 (contDiff_cylinderAngularParameters rotatedInput).contDiffAt

def cylinderPhaseSignDerivativeEquiv (x y : Bool) (a : ℝ) :
    ParameterSpace rotatedInput ≃L[ℝ] TargetSpace input :=
  (cylinderAngularDerivativeEquiv rotatedInput).trans (phaseSignDerivativeEquiv x y a)

theorem hasFDerivAt_cylinderPhaseSignDerivativeEquiv (x y : Bool) (a : ℝ) :
    HasFDerivAt (cylinderPhaseSignCoordinates x y a)
      (cylinderPhaseSignDerivativeEquiv x y a).toContinuousLinearMap 0 := by
  have h : HasFDerivAt (phaseSignCoordinates x y a)
      (phaseSignDerivativeEquiv x y a).toContinuousLinearMap
      (cylinderAngularParameters rotatedInput 0) := by
    rw [cylinderAngularParameters_zero]
    exact hasFDerivAt_phaseSignDerivativeEquiv x y a
  exact h.comp 0 (hasFDerivAt_cylinderAngularDerivativeEquiv rotatedInput)

theorem cylinderPhaseSignDerivative_relative_det_pos (x y : Bool) (a : ℝ) :
    0 < ((cylinderPhaseSignDerivativeEquiv x y a).trans
      (cylinderPhaseSignDerivativeEquiv true true 0).symm).toLinearMap.det := by
  have h := LocalBoundaryComparison.relativeDet_transport
    (phaseSignDerivativeEquiv x y a) (phaseSignDerivativeEquiv true true 0)
    (cylinderAngularDerivativeEquiv rotatedInput) (ContinuousLinearEquiv.refl ℝ (TargetSpace input))
  change ((cylinderPhaseSignDerivativeEquiv x y a).trans
    (cylinderPhaseSignDerivativeEquiv true true 0).symm).toLinearMap.det = _ at h
  rw [h]
  exact phaseSignDerivative_relative_det_pos x y a

def cylinderPhaseSignBoundary (x y : Bool) (a : ℝ) :
    LocalDegree.BoundaryData (cylinderPhaseSignCoordinates x y a)
      (cylinderPhaseSignDerivativeEquiv x y a) Set.univ :=
  Classical.choice (LocalDegree.nonempty_boundaryData_of_contDiffAt
    (cylinderPhaseSignDerivativeEquiv x y a) (hasFDerivAt_cylinderPhaseSignDerivativeEquiv x y a)
    (cylinderPhaseSignCoordinates_zero x y a) Filter.univ_mem
    (contDiffAt_cylinderPhaseSignCoordinates x y a))

theorem cylinderPhaseSignBoundary_homology_eq (x y : Bool) (a : ℝ) (k : ℕ) :
    singularHomologyMap (cylinderPhaseSignBoundary x y a).normalizedMap k =
      singularHomologyMap (cylinderPhaseSignBoundary true true 0).normalizedMap k :=
  LocalBoundaryComparison.normalized_homology_eq (parameterBasis rotatedInput)
    (cylinderPhaseSignBoundary x y a) (cylinderPhaseSignBoundary true true 0)
      (cylinderPhaseSignDerivative_relative_det_pos x y a) k

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
