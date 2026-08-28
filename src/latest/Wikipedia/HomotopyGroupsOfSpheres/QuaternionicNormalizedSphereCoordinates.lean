import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpherePreimageCoordinates

/-!
# One fixed normalization of the actual target-coordinate function

The inverse of the checked reference derivative identifies the target
coordinates with the common source parameter space. Every preimage chart
then has positive relative coordinate determinant. The function is used
on the preimage of the target chart, not asserted globally smooth.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

local notation "Coordinates" => EuclideanSpace ℝ (Fin 7)
local notation "Parameters" => ParameterSpace rotatedInput

attribute [local irreducible] cylinderPhaseSignDerivativeEquiv sourceEuclideanEquiv

def referenceDerivative : Parameters ≃L[ℝ] TargetSpace input :=
  cylinderPhaseSignDerivativeEquiv true true 0

def normalizedCandidateCoordinates : Sphere 7 → Parameters :=
  referenceDerivative.symm ∘ sphereCandidateCoordinates input

theorem normalizedCandidateCoordinates_preimageChart
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    normalizedCandidateCoordinates ∘ spherePreimageEuclideanChart u b =
      referenceDerivative.symm ∘ cylinderPhaseSignCoordinates b.1 b.2 (negativePhaseAngle u) ∘
        sourceEuclideanEquiv rotatedInput := by
  funext p
  change referenceDerivative.symm
    (sphereCandidateCoordinates input
      (spherePreimageSourceChart u b (sourceEuclideanEquiv rotatedInput p))) = _
  exact congrArg referenceDerivative.symm
    (congrFun (sphereCandidateCoordinates_preimageChart u hu b)
      (sourceEuclideanEquiv rotatedInput p))

theorem normalizedCandidateCoordinates_preimageChart_zero
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    (normalizedCandidateCoordinates ∘ spherePreimageEuclideanChart u b) 0 = 0 := by
  rw [normalizedCandidateCoordinates_preimageChart u hu]
  simp only [Function.comp_apply, map_zero, cylinderPhaseSignCoordinates_zero]

theorem contDiffAt_normalizedCandidateCoordinates_preimageChart
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    ContDiffAt ℝ ∞ (normalizedCandidateCoordinates ∘ spherePreimageEuclideanChart u b) 0 := by
  rw [normalizedCandidateCoordinates_preimageChart u hu]
  have h : ContDiffAt ℝ ∞ (cylinderPhaseSignCoordinates b.1 b.2 (negativePhaseAngle u))
      (sourceEuclideanEquiv rotatedInput 0) := by
    rw [map_zero]
    exact contDiffAt_cylinderPhaseSignCoordinates _ _ _
  exact referenceDerivative.symm.contDiff.contDiffAt.comp 0
    (h.comp 0 (sourceEuclideanEquiv rotatedInput).contDiff.contDiffAt)

def normalizedPreimageDerivative (u : unitary ℂ) (b : Bool × Bool) :
    Coordinates ≃L[ℝ] Parameters :=
  ((sourceEuclideanEquiv rotatedInput).trans
    (cylinderPhaseSignDerivativeEquiv b.1 b.2 (negativePhaseAngle u))).trans
      referenceDerivative.symm

theorem hasFDerivAt_normalizedPreimageDerivative
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    HasFDerivAt (normalizedCandidateCoordinates ∘ spherePreimageEuclideanChart u b)
      (normalizedPreimageDerivative u b).toContinuousLinearMap 0 := by
  rw [normalizedCandidateCoordinates_preimageChart u hu]
  have h : HasFDerivAt (cylinderPhaseSignCoordinates b.1 b.2 (negativePhaseAngle u))
      (cylinderPhaseSignDerivativeEquiv b.1 b.2 (negativePhaseAngle u)).toContinuousLinearMap
      (sourceEuclideanEquiv rotatedInput 0) := by
    rw [map_zero]
    exact hasFDerivAt_cylinderPhaseSignDerivativeEquiv _ _ _
  exact referenceDerivative.symm.toContinuousLinearMap.hasFDerivAt.comp 0
    (h.comp 0 ((sourceEuclideanEquiv rotatedInput).toContinuousLinearMap.hasFDerivAt (x := 0)))

theorem normalizedPreimageDerivative_relative_det_pos (u : unitary ℂ) (b : Bool × Bool) :
    0 < ((sourceEuclideanEquiv rotatedInput).symm.toContinuousLinearMap.comp
      (normalizedPreimageDerivative u b).toContinuousLinearMap).det := by
  let A := (cylinderPhaseSignDerivativeEquiv b.1 b.2 (negativePhaseAngle u)).trans
    referenceDerivative.symm
  let B := sourceEuclideanEquiv rotatedInput
  have h := LinearMap.det_conj A.toLinearMap B.symm.toLinearEquiv
  change (B.symm.toLinearMap.comp (A.toLinearMap.comp B.toLinearMap)).det = _ at h
  change 0 < (B.symm.toLinearMap.comp (A.toLinearMap.comp B.toLinearMap)).det
  rw [h]
  exact cylinderPhaseSignDerivative_relative_det_pos b.1 b.2 (negativePhaseAngle u)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
