import Wikipedia.NoExoticSixSphere.QuaternionSphereRotations
import Wikipedia.NoExoticSixSphere.OrthogonalColumnBundle

/-!
# A global section of the rank-four orthogonal column projection

Right multiplication by a unit quaternion carries the real unit to that
quaternion. Transporting the actual isometry to the existing Euclidean
coordinates gives a global continuous section, equal to the identity at
the distinguished column. No covering-space or homotopy calculation is
assumed here.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionColumnSection

open GLOrthonormalization OrthogonalPaths

def column : Sphere 3 := QuaternionSphere.sphereHomeomorph QuaternionSphere.one

def rotationEquiv (x : Sphere 3) : Vector 4 ≃ₗᵢ[ℝ] Vector 4 :=
  (Quaternion.linearIsometryEquivTuple.symm.trans
    (QuaternionSphere.rightIsometry (QuaternionSphere.sphereHomeomorph.symm x))).trans
    Quaternion.linearIsometryEquivTuple

def rotation (x : Sphere 3) : OrthogonalOperators 4 := ofEquiv (rotationEquiv x)

theorem rotation_apply (x : Sphere 3) (w : Vector 4) :
    (rotation x).val.val w = Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm w *
        (QuaternionSphere.sphereHomeomorph.symm x).val) := rfl

theorem continuous_rotation : Continuous rotation := by
  have h : Continuous (fun x : Sphere 3 ↦ (rotation x).val.val) := by
    apply continuous_clm_apply.mpr
    intro w
    simp only [rotation_apply]
    exact Quaternion.linearIsometryEquivTuple.continuous.comp
      (continuous_const.mul
        (continuous_subtype_val.comp QuaternionSphere.sphereHomeomorph.symm.continuous))
  exact (h.subtype_mk _).subtype_mk _

def sectionMap : C(Sphere 3, OrthogonalOperators 4) := ⟨rotation, continuous_rotation⟩

theorem rotation_column (x : Sphere 3) : (rotation x).val.val column.val = x.val := by
  rw [rotation_apply]
  change Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm (Quaternion.linearIsometryEquivTuple 1) *
      (QuaternionSphere.sphereHomeomorph.symm x).val) = x.val
  rw [LinearIsometryEquiv.symm_apply_apply, one_mul]
  exact congrArg Subtype.val (QuaternionSphere.sphereHomeomorph.apply_symm_apply x)

theorem rotation_basepoint : rotation column = identity 4 := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rw [rotation_apply]
  change Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm w *
      (QuaternionSphere.sphereHomeomorph.symm
        (QuaternionSphere.sphereHomeomorph QuaternionSphere.one)).val) = w
  rw [Homeomorph.symm_apply_apply]
  change Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm w * 1) = w
  rw [mul_one, LinearIsometryEquiv.apply_symm_apply]

end NoExoticSixSphere.QuaternionColumnSection
