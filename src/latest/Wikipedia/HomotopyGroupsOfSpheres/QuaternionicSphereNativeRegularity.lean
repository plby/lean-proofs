import Wikipedia.HomotopyGroupsOfSpheres.NativeRegularityFromChart
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicNormalizedSphereCoordinates

/-!
# Native regularity and positive normal signs at the actual twelve-point fiber

The checked source charts transfer differentiability and invertibility to
the original sphere atlas. The native chart-Jacobian factorization then
gives positive normal sign at every point of the actual selected fiber.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix
open Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

local notation "Parameters" => ParameterSpace rotatedInput

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local irreducible] normalizedCandidateCoordinates normalizedPreimageDerivative
  spherePreimageEuclideanChart sourceEuclideanEquiv sourceRadialEquiv

theorem zero_mem_spherePreimageEuclideanChart_source (u : unitary ℂ) (b : Bool × Bool) :
    0 ∈ (spherePreimageEuclideanChart u b).source := by
  rw [spherePreimageEuclideanChart_source]
  exact mem_univ _

theorem contMDiffAt_normalizedCandidateCoordinates_chartCenter
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    ContMDiffAt (𝓡 7) 𝓘(ℝ, Parameters) ∞ normalizedCandidateCoordinates
      (spherePreimageEuclideanChart u b 0) :=
  NativeRegularityFromChart.contMDiffAt_of_comp (spherePreimageEuclideanChart u b)
    (zero_mem_spherePreimageEuclideanChart_source u b)
    (contDiffAt_normalizedCandidateCoordinates_preimageChart u hu b)

theorem isInvertible_normalizedCandidateCoordinates_chartCenter
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    (mfderiv (𝓡 7) 𝓘(ℝ, Parameters) normalizedCandidateCoordinates
      (spherePreimageEuclideanChart u b 0)).IsInvertible :=
  NativeRegularityFromChart.isInvertible_mfderiv_of_comp (spherePreimageEuclideanChart u b)
    (zero_mem_spherePreimageEuclideanChart_source u b)
    (contDiffAt_normalizedCandidateCoordinates_preimageChart u hu b)
    (normalizedPreimageDerivative u b) (hasFDerivAt_normalizedPreimageDerivative u hu b)

theorem contMDiffAt_normalizedCandidateCoordinates_target (x : Sphere 7)
    (hx : x ∈ sphereCandidateTargetPreimage) :
    ContMDiffAt (𝓡 7) 𝓘(ℝ, Parameters) ∞ normalizedCandidateCoordinates x := by
  obtain ⟨r, b, he⟩ := targetPreimage_has_coherent_chart x hx
  exact he ▸ contMDiffAt_normalizedCandidateCoordinates_chartCenter
    (midpointPhases r) (midpointPhases_cube r) b

theorem normalizedCandidateCoordinates_target_zero (x : Sphere 7)
    (hx : x ∈ sphereCandidateTargetPreimage) : normalizedCandidateCoordinates x = 0 := by
  obtain ⟨r, b, he⟩ := targetPreimage_has_coherent_chart x hx
  have h : normalizedCandidateCoordinates (spherePreimageEuclideanChart (midpointPhases r) b 0)
      = 0 := normalizedCandidateCoordinates_preimageChart_zero _ (midpointPhases_cube r) b
  exact he ▸ h

theorem isInvertible_normalizedCandidateCoordinates_target (x : Sphere 7)
    (hx : x ∈ sphereCandidateTargetPreimage) :
    (mfderiv (𝓡 7) 𝓘(ℝ, Parameters) normalizedCandidateCoordinates x).IsInvertible := by
  obtain ⟨r, b, he⟩ := targetPreimage_has_coherent_chart x hx
  exact he ▸ isInvertible_normalizedCandidateCoordinates_chartCenter
    (midpointPhases r) (midpointPhases_cube r) b

theorem normalizedCandidateNormalSign_chartCenter
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    SignType.sign (normalJacobian (sourceRadialEquiv rotatedInput)
      (spherePreimageEuclideanChart u b 0)
      (mfderiv (𝓡 7) 𝓘(ℝ, Parameters) normalizedCandidateCoordinates
        (spherePreimageEuclideanChart u b 0))) = 1 := by
  have h := chartJacobian_sign_factor (spherePreimageEuclideanChart u b)
    (sourceRadialEquiv rotatedInput) (sourceEuclideanEquiv rotatedInput)
    (zero_mem_spherePreimageEuclideanChart_source u b) normalizedCandidateCoordinates
    ((contMDiffAt_normalizedCandidateCoordinates_chartCenter u hu b).mdifferentiableAt (by simp))
    (isInvertible_normalizedCandidateCoordinates_chartCenter u hu b)
  rw [spherePreimageEuclideanChart_sign, one_mul,
    (hasFDerivAt_normalizedPreimageDerivative u hu b).fderiv] at h
  exact h.symm.trans (sign_eq_one_iff.mpr (normalizedPreimageDerivative_relative_det_pos u b))

theorem normalizedCandidateNormalSign_target (x : Sphere 7)
    (hx : x ∈ sphereCandidateTargetPreimage) :
    SignType.sign (normalJacobian (sourceRadialEquiv rotatedInput) x
      (mfderiv (𝓡 7) 𝓘(ℝ, Parameters) normalizedCandidateCoordinates x)) = 1 := by
  obtain ⟨r, b, he⟩ := targetPreimage_has_coherent_chart x hx
  exact he ▸ normalizedCandidateNormalSign_chartCenter
    (midpointPhases r) (midpointPhases_cube r) b

theorem normalizedCandidateNormalJacobian_target_pos (x : Sphere 7)
    (hx : x ∈ sphereCandidateTargetPreimage) :
    0 < normalJacobian (sourceRadialEquiv rotatedInput) x
      (mfderiv (𝓡 7) 𝓘(ℝ, Parameters) normalizedCandidateCoordinates x) :=
  sign_eq_one_iff.mp (normalizedCandidateNormalSign_target x hx)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
