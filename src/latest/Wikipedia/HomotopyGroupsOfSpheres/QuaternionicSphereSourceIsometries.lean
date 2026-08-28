import Wikipedia.HomotopyGroupsOfSpheres.SphereCylinderIsometries
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereSourceCharts

/-!
# Source symmetries on the actual seven-sphere

Conjugate the original real isometry into the chosen six real coordinates,
then fix each of the two cylinder coordinates. This transports the actual
source chart and retains the original ambient determinant.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open NoExoticSixSphere SphereCenteredCoordinates

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)
local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 8)

def realSourceIsometry (e : Ambient ≃ₗᵢ[ℝ] Ambient) :
    EuclideanSpace ℝ (Fin 6) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 6) :=
  (complexRealCoordinates.symm.trans e).trans complexRealCoordinates

theorem realSourceIsometry_det (e : Ambient ≃ₗᵢ[ℝ] Ambient) :
    (realSourceIsometry e).toLinearEquiv.toLinearMap.det = e.toLinearEquiv.toLinearMap.det :=
  LinearMap.det_conj e.toLinearEquiv.toLinearMap complexRealCoordinates.toLinearEquiv

theorem realSourceIsometry_sphere (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere) :
    sphereIsometry (realSourceIsometry e) (sphereFiveHomeomorph.symm z) =
      sphereFiveHomeomorph.symm (sphereIsometry e z) := by
  apply Subtype.ext
  change complexRealCoordinates
    (e (complexRealCoordinates.symm (complexRealCoordinates z.val))) =
      complexRealCoordinates (e z.val)
  rw [complexRealCoordinates.symm_apply_apply]

def sphereSourceIsometry (e : Ambient ≃ₗᵢ[ℝ] Ambient) : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient :=
  CylinderLatitude.liftIsometry (CylinderLatitude.liftIsometry (realSourceIsometry e))

theorem sphereSourceIsometry_det (e : Ambient ≃ₗᵢ[ℝ] Ambient) :
    (sphereSourceIsometry e).toLinearEquiv.toLinearMap.det = e.toLinearEquiv.toLinearMap.det := by
  rw [sphereSourceIsometry, CylinderLatitude.liftIsometry_det,
    CylinderLatitude.liftIsometry_det, realSourceIsometry_det]

def sourceParameterIsometry (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere) :
    ParameterSpace z ≃L[ℝ] ParameterSpace (sphereIsometry e z) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (tangentIsometry e z).toContinuousLinearEquiv)

theorem sphereSourceChart_natural (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (p : ParameterSpace z) :
    sphereIsometry (sphereSourceIsometry e) (sphereSourceChart z p) =
      sphereSourceChart (sphereIsometry e z) (sourceParameterIsometry e z p) := by
  rw [sphereSourceChart_apply]
  change sphereIsometry (CylinderLatitude.liftIsometry
    (CylinderLatitude.liftIsometry (realSourceIsometry e)))
      (SphereCylinder.point 6
        (p.1, SphereCylinder.point 5 (p.2.1, sphereFiveHomeomorph.symm (localSphere z p)))) = _
  rw [CylinderLatitude.sphereIsometry_lift_point, CylinderLatitude.sphereIsometry_lift_point,
    realSourceIsometry_sphere, sphereSourceChart_apply]
  change SphereCylinder.point 6 (p.1, SphereCylinder.point 5
    (p.2.1, sphereFiveHomeomorph.symm (sphereIsometry e (inverse z p.2.2)))) =
      SphereCylinder.point 6 (p.1, SphereCylinder.point 5
        (p.2.1, sphereFiveHomeomorph.symm
          (inverse (sphereIsometry e z) (tangentIsometry e z p.2.2))))
  rw [inverse_tangentIsometry]

theorem sphereSourceIsometry_midpoint (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere) :
    sphereIsometry (sphereSourceIsometry e) (midpointSphereEmbedding z) =
      midpointSphereEmbedding (sphereIsometry e z) := by
  have h := sphereSourceChart_natural e z 0
  simpa only [sphereSourceChart_zero, map_zero] using h

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def transportedSphereSourceChart (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere) :
    PartialDiffeomorph 𝓘(ℝ, ParameterSpace z) (𝓡 7) (ParameterSpace z) (Sphere 7) ∞ :=
  (sphereSourceChart z).trans
    (sphereIsometryDiffeomorph 7 (sphereSourceIsometry e)).toPartialDiffeomorph

theorem transportedSphereSourceChart_apply (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (p : ParameterSpace z) :
    transportedSphereSourceChart e z p =
      sphereIsometry (sphereSourceIsometry e) (sphereSourceChart z p) := rfl

theorem transportedSphereSourceChart_source (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere) :
    (transportedSphereSourceChart e z).source = univ := by
  apply Set.eq_univ_of_forall
  intro p
  refine ⟨?_, mem_univ _⟩
  change p ∈ (sphereSourceChart z).source
  rw [sphereSourceChart_source]
  exact mem_univ _

theorem transportedSphereSourceChart_zero (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere) :
    transportedSphereSourceChart e z 0 = midpointSphereEmbedding (sphereIsometry e z) := by
  rw [transportedSphereSourceChart_apply, sphereSourceChart_zero, sphereSourceIsometry_midpoint]

theorem transportedSphereSourceChart_is_centered (e : Ambient ≃ₗᵢ[ℝ] Ambient) (z : UnitSphere)
    (p : ParameterSpace z) :
    transportedSphereSourceChart e z p =
      sphereSourceChart (sphereIsometry e z) (sourceParameterIsometry e z p) :=
  sphereSourceChart_natural e z p

theorem contDiff_sphereSourceChart_val (z : UnitSphere) :
    ContDiff ℝ ∞ (fun p : ParameterSpace z ↦ (sphereSourceChart z p).val) :=
  (contMDiff_coe_sphere.comp (contMDiff_sphereSourceChart z)).contDiff

theorem hasFDerivAt_transportedSphereSourceChart (e : Ambient ≃ₗᵢ[ℝ] Ambient)
    (z : UnitSphere) :
    HasFDerivAt (fun p : ParameterSpace z ↦ (transportedSphereSourceChart e z p).val)
      ((sphereSourceIsometry e).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fun p : ParameterSpace z ↦ (sphereSourceChart z p).val) 0)) 0 :=
  (sphereSourceIsometry e).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp 0
    (((contDiff_sphereSourceChart_val z).differentiable (by simp) 0).hasFDerivAt)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
