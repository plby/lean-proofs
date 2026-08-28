import Wikipedia.NoExoticSixSphere.QuaternionicHopfNativeClass

/-!
# An actual non-basepoint fiber of the quaternionic Hopf polynomial

The south target is distinct from the original based pole. Its fiber is
exactly the second quaternionic axis. This retains the original polynomial,
sphere coordinates and smooth axis inclusion, so this fiber can be used
inside the smash construction without being collapsed to the basepoint.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthFiber

open NoExoticSixSphere QuaternionicHopf
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def point : Sphere 4 :=
  ⟨-(spherePole 4).val, by
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp (spherePole 4).property⟩

theorem point_ne_pole : point ≠ spherePole 4 := by
  intro h
  have hh := congrArg (fun x : Sphere 4 ↦ x.val 0) h
  norm_num [point, spherePole] at hh

theorem point_join : SphereCylinder.join 3 (-1, (0 : V 4)) = point.val := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [point, spherePole]
  · simp [point, spherePole, Fin.succ_ne_zero]

def axis : V 4 →ₗᵢ[ℝ] V 8 where
  toLinearMap := planeCoordinates.toLinearMap.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ).symm.toLinearMap.comp
      (LinearMap.inr ℝ ℍ ℍ)).comp Quaternion.linearIsometryEquivTuple.symm.toLinearMap)
  norm_map' v := by
    change ‖planeCoordinates (WithLp.toLp 2
      ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm v))‖ = ‖v‖
    rw [planeCoordinates.norm_map, WithLp.norm_toLp_snd,
      Quaternion.linearIsometryEquivTuple.symm.norm_map]

theorem first_axis (v : V 4) : first (axis v) = 0 := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm v)))).fst = 0
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_axis (v : V 4) : second (axis v) = Quaternion.linearIsometryEquivTuple.symm v := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm v)))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem axis_second_of_first_eq_zero (x : V 8) (hx : first x = 0) :
    axis (Quaternion.linearIsometryEquivTuple (second x)) = x := by
  change planeCoordinates (WithLp.toLp 2
    ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm
      (Quaternion.linearIsometryEquivTuple (second x)))) = x
  rw [LinearIsometryEquiv.symm_apply_apply, ← hx]
  exact planeCoordinates.apply_symm_apply x

theorem sphereMap_eq_point_iff (x : Sphere 7) : sphereMap x = point ↔ first x.val = 0 := by
  have hs := normSq_sum x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow] at hs
  constructor
  · intro hx
    have hh := congrArg (fun y : Sphere 4 ↦ y.val 0) hx
    change Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val) = -1 at hh
    apply Quaternion.normSq_eq_zero.mp
    linarith
  · intro hx
    have hb : Quaternion.normSq (second x.val) = 1 := by
      simpa only [hx, map_zero, zero_add] using hs
    apply Subtype.ext
    change SphereCylinder.join 3
      (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val),
        Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (first x.val * star (second x.val)))) = _
    simp only [hb, hx, map_zero, zero_sub, zero_mul, smul_zero]
    exact point_join

theorem axis_mem_sphere (q : Sphere 3) : axis q.val ∈ Sphere 7 := by
  rw [mem_sphere_zero_iff_norm, axis.norm_map]
  exact mem_sphere_zero_iff_norm.mp q.property

def fiberPoint : C(Sphere 3, Sphere 7) :=
  ⟨fun q ↦ ⟨axis q.val, axis_mem_sphere q⟩,
    (axis.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem first_fiberPoint (q : Sphere 3) : first (fiberPoint q).val = 0 := first_axis q.val

theorem second_fiberPoint (q : Sphere 3) :
    second (fiberPoint q).val = Quaternion.linearIsometryEquivTuple.symm q.val := second_axis q.val

theorem sphereMap_fiberPoint (q : Sphere 3) : sphereMap (fiberPoint q) = point :=
  (sphereMap_eq_point_iff _).mpr (first_fiberPoint q)

theorem fiberPoint_ne_pole (q : Sphere 3) : fiberPoint q ≠ spherePole 7 := by
  intro h
  apply point_ne_pole
  rw [← sphereMap_fiberPoint q, h, QuaternionicHopf.sphereMap_pole]

theorem contMDiff_fiberPoint : ContMDiff (𝓡 3) (𝓡 7) ∞ fiberPoint := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (axis.toContinuousLinearMap.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
    (fun q ↦ (fiberPoint q).property)

def fiberInverse (x : {x : Sphere 7 // sphereMap x = point}) : Sphere 3 :=
  ⟨Quaternion.linearIsometryEquivTuple (second x.val.val), by
    rw [mem_sphere_zero_iff_norm, Quaternion.linearIsometryEquivTuple.norm_map]
    have hs := normSq_sum x.val.val
    rw [(sphereMap_eq_point_iff x.val).mp x.property, map_zero, zero_add,
      mem_sphere_zero_iff_norm.mp x.val.property, one_pow] at hs
    rw [Quaternion.normSq_eq_norm_mul_self] at hs
    nlinarith [norm_nonneg (second x.val.val)]⟩

theorem fiberInverse_fiberPoint (q : Sphere 3) :
    fiberInverse ⟨fiberPoint q, sphereMap_fiberPoint q⟩ = q := by
  apply Subtype.ext
  change Quaternion.linearIsometryEquivTuple (second (fiberPoint q).val) = q.val
  rw [second_fiberPoint, LinearIsometryEquiv.apply_symm_apply]

theorem fiberPoint_fiberInverse (x : {x : Sphere 7 // sphereMap x = point}) :
    fiberPoint (fiberInverse x) = x.val := by
  apply Subtype.ext
  exact axis_second_of_first_eq_zero x.val.val ((sphereMap_eq_point_iff x.val).mp x.property)

def fiberHomeomorph : Sphere 3 ≃ₜ {x : Sphere 7 // sphereMap x = point} where
  toFun q := ⟨fiberPoint q, sphereMap_fiberPoint q⟩
  invFun := fiberInverse
  left_inv := fiberInverse_fiberPoint
  right_inv x := Subtype.ext (fiberPoint_fiberInverse x)
  continuous_toFun := fiberPoint.continuous.subtype_mk _
  continuous_invFun := (Quaternion.linearIsometryEquivTuple.continuous.comp
    (second.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSouthFiber
