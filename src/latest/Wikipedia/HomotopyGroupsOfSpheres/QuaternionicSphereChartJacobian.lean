import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereOutwardFrames
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseBoundaryHomology
import Wikipedia.SmoothSixDPoincare.SphereLocalDegreeOrientation

/-!
# The outward signs in the native local-degree convention

Use one fixed real seven-dimensional parameter basis. After this linear
reparametrization, the actual chart Jacobian relative to the base radial
frame is exactly the determinant of the original source isometry.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)
local notation "Coordinates" => EuclideanSpace ℝ (Fin 7)

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sourceEuclideanEquiv (z : UnitSphere) : Coordinates ≃L[ℝ] ParameterSpace z :=
  LinearEquiv.toContinuousLinearEquiv
    ((WithLp.linearEquiv 2 ℝ (Fin 7 → ℝ)).trans (parameterBasis z).equivFun.symm)

def euclideanSourceChart (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (B : Coordinates ≃L[ℝ] ParameterSpace z) :
    PartialDiffeomorph (𝓡 7) (𝓡 7) Coordinates (Sphere 7) ∞ :=
  B.toDiffeomorph.toPartialDiffeomorph.trans (transportedSphereSourceChart e z)

theorem euclideanSourceChart_apply (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (B : Coordinates ≃L[ℝ] ParameterSpace z) (p : Coordinates) :
    euclideanSourceChart e z B p = transportedSphereSourceChart e z (B p) := rfl

theorem euclideanSourceChart_source (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (B : Coordinates ≃L[ℝ] ParameterSpace z) : (euclideanSourceChart e z B).source = univ := by
  apply Set.eq_univ_of_forall
  intro p
  refine ⟨mem_univ _, ?_⟩
  change B p ∈ (transportedSphereSourceChart e z).source
  rw [transportedSphereSourceChart_source]
  exact mem_univ _

theorem euclideanSourceChart_radialFrame (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (B : Coordinates ≃L[ℝ] ParameterSpace z) :
    chartRadialFrame (euclideanSourceChart e z B) 0 =
      (chartRadialFrame (transportedSphereSourceChart e z) 0).comp
        ((ContinuousLinearMap.id ℝ ℝ).prodMap B.toContinuousLinearMap) := by
  have h := hasFDerivAt_transportedSphereSourceChart e z
  have h' : HasFDerivAt
      (fun p : ParameterSpace z ↦ (transportedSphereSourceChart e z p).val)
      (fderiv ℝ (fun p : ParameterSpace z ↦ (transportedSphereSourceChart e z p).val) 0)
      (B 0) := by
    rw [map_zero, h.fderiv]
    exact h
  have hc := h'.comp 0 (B.toContinuousLinearMap.hasFDerivAt (x := 0))
  change HasFDerivAt (fun v : Coordinates ↦
    (transportedSphereSourceChart e z (B v)).val) _ 0 at hc
  apply ContinuousLinearMap.ext
  intro p
  change p.1 • (transportedSphereSourceChart e z (B 0)).val +
      fderiv ℝ (fun v : Coordinates ↦ (transportedSphereSourceChart e z (B v)).val) 0 p.2 =
    p.1 • (transportedSphereSourceChart e z 0).val +
      fderiv ℝ (fun v : ParameterSpace z ↦ (transportedSphereSourceChart e z v).val) 0 (B p.2)
  rw [map_zero, hc.fderiv]
  rfl

theorem euclideanSourceChart_jacobian (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (B : Coordinates ≃L[ℝ] ParameterSpace z) :
    chartJacobian (euclideanSourceChart e z B) (sourceRadialEquiv z) B 0 =
      e.toLinearEquiv.toLinearMap.det := by
  let Q := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr B
  have hQ : Q.toContinuousLinearMap.comp
      (Q.trans (sourceRadialEquiv z)).symm.toContinuousLinearMap =
        (sourceRadialEquiv z).symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact Q.apply_symm_apply ((sourceRadialEquiv z).symm v)
  change ((chartRadialFrame (euclideanSourceChart e z B) 0).comp
    (Q.trans (sourceRadialEquiv z)).symm.toContinuousLinearMap).det = _
  rw [euclideanSourceChart_radialFrame, ContinuousLinearMap.comp_assoc]
  change ((chartRadialFrame (transportedSphereSourceChart e z) 0).comp
    (Q.toContinuousLinearMap.comp
      (Q.trans (sourceRadialEquiv z)).symm.toContinuousLinearMap)).det = _
  rw [hQ]
  exact transportedSphereSourceChart_relativeDet e z

namespace MidpointSeed

def spherePreimageEuclideanChart (u : unitary ℂ) (b : Bool × Bool) :
    PartialDiffeomorph (𝓡 7) (𝓡 7) Coordinates (Sphere 7) ∞ :=
  euclideanSourceChart (preimageSourceIsometry u b) rotatedInput
    (sourceEuclideanEquiv rotatedInput)

theorem spherePreimageEuclideanChart_source (u : unitary ℂ) (b : Bool × Bool) :
    (spherePreimageEuclideanChart u b).source = univ :=
  euclideanSourceChart_source _ _ _

theorem spherePreimageEuclideanChart_zero (u : unitary ℂ) (b : Bool × Bool) :
    spherePreimageEuclideanChart u b 0 = midpointSphereEmbedding (phaseInput u b) := by
  change transportedSphereSourceChart (preimageSourceIsometry u b) rotatedInput
    (sourceEuclideanEquiv rotatedInput 0) = _
  rw [map_zero]
  exact spherePreimageSourceChart_zero u b

theorem spherePreimageEuclideanChart_jacobian_pos (u : unitary ℂ) (b : Bool × Bool) :
    0 < chartJacobian (spherePreimageEuclideanChart u b) (sourceRadialEquiv rotatedInput)
      (sourceEuclideanEquiv rotatedInput) 0 := by
  rw [spherePreimageEuclideanChart, euclideanSourceChart_jacobian]
  exact preimageSourceIsometry_det_pos u b

theorem spherePreimageEuclideanChart_sign (u : unitary ℂ) (b : Bool × Bool) :
    SignType.sign (chartJacobian (spherePreimageEuclideanChart u b)
      (sourceRadialEquiv rotatedInput) (sourceEuclideanEquiv rotatedInput) 0) = 1 :=
  sign_eq_one_iff.mpr (spherePreimageEuclideanChart_jacobian_pos u b)

end MidpointSeed

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
