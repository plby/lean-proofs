import Wikipedia.NoExoticSixSphere.QuaternionSphere

/-!
# The actual antipodal map of the three-sphere is homotopic to the identity

A path from the real unit to its negative in the actual unit quaternions
acts by quaternion multiplication. The coordinate isometry transports that
homotopy to the original Euclidean three-sphere, retaining the exact endpoints.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.SphereThreeAntipodal

open GLOrthonormalization

def map : C(Sphere 3, Sphere 3) :=
  ⟨antipode, continuous_subtype_val.neg.subtype_mk _⟩

def homotopy : (ContinuousMap.id (Sphere 3)).Homotopy map := by
  let h := QuaternionSphere.sphereHomeomorph
  let p := PathConnectedSpace.somePath QuaternionSphere.one
    (antipode QuaternionSphere.one)
  refine {
    toFun := fun z ↦ h (QuaternionSphere.multiply (p z.1, h.symm z.2))
    continuous_toFun := h.continuous.comp (QuaternionSphere.multiply.continuous.comp
      ((p.continuous.comp continuous_fst).prodMk (h.symm.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro x
    change h (QuaternionSphere.multiply (p 0, h.symm x)) = x
    rw [p.source, QuaternionSphere.multiply_one_left, h.apply_symm_apply]
  · intro x
    change h (QuaternionSphere.multiply (p 1, h.symm x)) = antipode x
    rw [p.target]
    apply Subtype.ext
    change Quaternion.linearIsometryEquivTuple
      ((-1 : ℍ) * Quaternion.linearIsometryEquivTuple.symm x.val) = -x.val
    rw [neg_one_mul, map_neg, LinearIsometryEquiv.apply_symm_apply]

end NoExoticSixSphere.SphereThreeAntipodal
