import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPhaseOrientation
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-!
# The scalar source action preserves ambient orientation

Unit complex multiplication is a real linear isometry. Its determinant on
the six-dimensional real ambient space is one, and it transports the actual
stereographic source charts. At cube roots it identifies the phase family
with the original projected map at the corresponding scalar preimage.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicSymmetricMatrices

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)

def scalarComplexEquiv (q : unitary ℂ) : Ambient ≃ₗ[ℂ] Ambient :=
  LinearEquiv.smulOfNeZero ℂ Ambient q.val (unitary_complex_ne_zero q)

def scalarRealIsometry (q : unitary ℂ) : Ambient ≃ₗᵢ[ℝ] Ambient where
  __ := (scalarComplexEquiv q).restrictScalars ℝ
  norm_map' v := by
    change ‖q.val • v‖ = ‖v‖
    rw [norm_smul, unitary_complex_norm, one_mul]

theorem scalarRealIsometry_apply (q : unitary ℂ) (v : Ambient) :
    scalarRealIsometry q v = q.val • v := rfl

theorem scalarRealIsometry_det (q : unitary ℂ) :
    (scalarRealIsometry q).toLinearEquiv.toLinearMap.det = 1 := by
  change ((scalarComplexEquiv q).toLinearMap.restrictScalars ℝ).det = 1
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  have he : (scalarComplexEquiv q).toLinearMap = q.val • (LinearMap.id : Ambient →ₗ[ℂ] Ambient) :=
    LinearMap.ext (fun _ ↦ rfl)
  rw [he, LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp [unitary_normSq]

theorem scalar_sphereIsometry (q : unitary ℂ) (z : UnitSphere) :
    SphereCenteredCoordinates.sphereIsometry (scalarRealIsometry q) z = scalarSphere q z := by
  apply Subtype.ext
  rfl

def scalarParameterEquiv (q : unitary ℂ) (z : UnitSphere) :
    ParameterSpace z ≃L[ℝ] ParameterSpace (scalarSphere q z) := by
  let e := LinearIsometryEquiv.toContinuousLinearEquiv
    (SphereCenteredCoordinates.tangentIsometry (scalarRealIsometry q) z)
  have he : SphereCenteredCoordinates.sphereIsometry (scalarRealIsometry q) z =
      scalarSphere q z := scalar_sphereIsometry q z
  rw [he] at e
  exact (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e)

theorem scalarParameterEquiv_fst (q : unitary ℂ) (z : UnitSphere) (p : ParameterSpace z) :
    (scalarParameterEquiv q z p).1 = p.1 := by
  unfold scalarParameterEquiv
  rfl

theorem scalarParameterEquiv_snd_fst (q : unitary ℂ) (z : UnitSphere) (p : ParameterSpace z) :
    (scalarParameterEquiv q z p).2.1 = p.2.1 := by
  unfold scalarParameterEquiv
  rfl

theorem localSphere_scalarParameterEquiv (q : unitary ℂ) (z : UnitSphere) (p : ParameterSpace z) :
    localSphere (scalarSphere q z) (scalarParameterEquiv q z p) =
      scalarSphere q (localSphere z p) := by
  have he := SphereCenteredCoordinates.inverse_tangentIsometry (scalarRealIsometry q) z p.2.2
  simp only [scalar_sphereIsometry] at he
  exact he

theorem scalar_cube_projection_coordinates (q : Circle) (hq : (q : ℂ) ^ 3 = 1)
    (z : UnitSphere) (p : ParameterSpace z) :
    localProjection (scalarSphere (circleUnitary q) z)
      (scalarParameterEquiv (circleUnitary q) z p) =
        firstColumnFormula (Real.pi / 2 + p.1) (Real.pi / 2 + p.2.1)
          (scale q (symmetricMap (localSphere z p))) := by
  rw [localProjection, scalarParameterEquiv_fst, scalarParameterEquiv_snd_fst,
    localSphere_scalarParameterEquiv]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact symmetricMap_scalarSphere (circleUnitary q) hq (localSphere z p)

theorem phaseProjection_scalar_coordinates (z : UnitSphere) (a : ℝ)
    (ha : (Circle.exp a : ℂ) ^ 3 = 1) (p : ParameterSpace z) :
    phaseProjection z a p =
      localProjection (scalarSphere (circleUnitary (Circle.exp a)) z)
        (scalarParameterEquiv (circleUnitary (Circle.exp a)) z p) :=
  (scalar_cube_projection_coordinates (Circle.exp a) ha z p).symm

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
