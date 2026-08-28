import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereSourceCharts
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedLocalInverse

/-!
# The actual projected differential in seven-sphere cylinder charts

The two angular derivatives multiply by `π / 2` and the five tangent
coordinates are unchanged. This change is an orientation-preserving
linear equivalence. Composing it with the original projected derivative
gives the derivative of the actual global map in the new source chart.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

def angleDerivativeEquiv : ℝ ≃L[ℝ] ℝ :=
  Units.mk0 (Real.pi / 2) (ne_of_gt angleOffset_derivative_pos) •
    ContinuousLinearEquiv.refl ℝ ℝ

@[simp] theorem angleDerivativeEquiv_apply (s : ℝ) :
    angleDerivativeEquiv s = (Real.pi / 2) * s := rfl

theorem angleDerivativeEquiv_linear : angleDerivativeEquiv.toLinearMap =
    (Real.pi / 2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := rfl

theorem hasFDerivAt_angleDerivativeEquiv :
    HasFDerivAt angleOffset angleDerivativeEquiv.toContinuousLinearMap 0 := by
  convert hasDerivAt_angleOffset_zero.hasFDerivAt using 1 <;> try rfl
  ext
  simp [mul_comm]

end Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicColumns SphereCenteredCoordinates

def cylinderAngularDerivativeEquiv (z : UnitSphere) : ParameterSpace z ≃L[ℝ] ParameterSpace z :=
  CylinderLatitude.angleDerivativeEquiv.prodCongr
    (CylinderLatitude.angleDerivativeEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (Tangent z)))

theorem cylinderAngularDerivativeEquiv_apply (z : UnitSphere) (p : ParameterSpace z) :
    cylinderAngularDerivativeEquiv z p = ((Real.pi / 2) * p.1, (Real.pi / 2) * p.2.1, p.2.2) := rfl

theorem cylinderAngularDerivativeEquiv_det (z : UnitSphere) :
    (cylinderAngularDerivativeEquiv z).toLinearMap.det = (Real.pi / 2) ^ 2 := by
  change (LinearMap.prodMap CylinderLatitude.angleDerivativeEquiv.toLinearMap
    (LinearMap.prodMap CylinderLatitude.angleDerivativeEquiv.toLinearMap
      (LinearMap.id : Tangent z →ₗ[ℝ] Tangent z))).det = _
  rw [LinearMap.det_prodMap, LinearMap.det_prodMap, CylinderLatitude.angleDerivativeEquiv_linear,
    LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id]
  simp [Module.finrank_self, pow_two]

theorem cylinderAngularDerivativeEquiv_det_pos (z : UnitSphere) :
    0 < (cylinderAngularDerivativeEquiv z).toLinearMap.det := by
  rw [cylinderAngularDerivativeEquiv_det]
  positivity

theorem hasFDerivAt_cylinderAngularDerivativeEquiv (z : UnitSphere) :
    HasFDerivAt (cylinderAngularParameters z)
      (cylinderAngularDerivativeEquiv z).toContinuousLinearMap 0 := by
  have h := CylinderLatitude.hasFDerivAt_angleDerivativeEquiv
  exact HasFDerivAt.prodMap (0 : ParameterSpace z) h
    (HasFDerivAt.prodMap (0 : ℝ × Tangent z) h (hasFDerivAt_id (0 : Tangent z)))

def sphereCandidateQuaternionMap (x : Sphere 7) :
    SphereCenteredCoordinates.UnitSphere (QuaternionSpace 1) :=
  ⟨WithLp.toLp 2 (sphereCandidateProjection x).val, mem_sphere_zero_iff_norm.mpr
    ((pairing_self_eq_one_iff_norm _).mp (sphereCandidateProjection x).property)⟩

theorem sphereCandidateQuaternionMap_sourceChart (z : UnitSphere) (p : ParameterSpace z) :
    sphereCandidateQuaternionMap (sphereSourceChart z p) =
      localColumn z (cylinderAngularParameters z p) := by
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2) (sphereCandidateProjection_sourceChart z p)

def sphereCandidateCoordinates (z : UnitSphere) (x : Sphere 7) : TargetSpace z :=
  chart (localColumn z 0) (sphereCandidateQuaternionMap x)

theorem sphereCandidateCoordinates_sourceChart (z : UnitSphere) :
    sphereCandidateCoordinates z ∘ sphereSourceChart z =
      localCoordinateMap z ∘ cylinderAngularParameters z := by
  funext p
  exact congrArg (chart (localColumn z 0)) (sphereCandidateQuaternionMap_sourceChart z p)

theorem sphereCandidateCoordinates_midpoint (z : UnitSphere) :
    sphereCandidateCoordinates z (midpointSphereEmbedding z) = 0 := by
  have h := congrFun (sphereCandidateCoordinates_sourceChart z) 0
  simpa only [Function.comp_apply, sphereSourceChart_zero, cylinderAngularParameters_zero,
    localCoordinateMap_zero] using h

theorem contDiffAt_sphereCandidateCoordinates_sourceChart (z : UnitSphere) {n : ℕ∞ω} :
    ContDiffAt ℝ n (sphereCandidateCoordinates z ∘ sphereSourceChart z) 0 := by
  rw [sphereCandidateCoordinates_sourceChart]
  have h : ContDiffAt ℝ n (localCoordinateMap z) (cylinderAngularParameters z 0) := by
    rw [cylinderAngularParameters_zero]
    exact contDiffAt_localCoordinateMap z
  exact h.comp 0 (contDiff_cylinderAngularParameters z).contDiffAt

def sphereCandidateCoordinateDerivativeEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    ParameterSpace z ≃L[ℝ] TargetSpace z :=
  (cylinderAngularDerivativeEquiv z).trans (localCoordinateDerivativeEquiv z hz)

theorem hasFDerivAt_sphereCandidateCoordinateDerivativeEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    HasFDerivAt (sphereCandidateCoordinates z ∘ sphereSourceChart z)
      (sphereCandidateCoordinateDerivativeEquiv z hz).toContinuousLinearMap 0 := by
  rw [sphereCandidateCoordinates_sourceChart]
  have h : HasFDerivAt (localCoordinateMap z)
      (localCoordinateDerivativeEquiv z hz).toContinuousLinearMap
      (cylinderAngularParameters z 0) := by
    rw [cylinderAngularParameters_zero]
    exact hasFDerivAt_localCoordinateDerivativeEquiv z hz
  exact h.comp 0 (hasFDerivAt_cylinderAngularDerivativeEquiv z)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
