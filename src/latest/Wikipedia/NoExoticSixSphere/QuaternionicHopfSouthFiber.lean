import Wikipedia.NoExoticSixSphere.QuaternionicHopfNorthFiber

/-!
# A nonbasepoint fiber of the explicit quaternionic Hopf map

The south pole is different from the based north pole. Its actual fiber
is the second quaternionic axis, with the standard smooth S3 parametrization.
This is the fiber suitable for a later noncollapsed product-fiber calculation.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def south : Sphere 4 := ⟨-(spherePole 4).val, by
  rw [mem_sphere_zero_iff_norm, norm_neg]
  exact mem_sphere_zero_iff_norm.mp (spherePole 4).property⟩

theorem south_ne_pole : south ≠ spherePole 4 := by
  intro h
  have he := congrArg (fun y : Sphere 4 ↦ y.val 0) h
  change -(1 : ℝ) = 1 at he
  norm_num at he

theorem south_join : SphereCylinder.join 3 (-1, (0 : V 4)) = south.val := by
  change SphereCylinder.join 3 (-1, (0 : V 4)) = -(spherePole 4).val
  have h := congrArg (fun v : V 5 ↦ -v) pole_join
  simpa only [← map_neg, Prod.neg_mk, neg_zero] using h

theorem sphereMap_eq_south_iff (x : Sphere 7) : sphereMap x = south ↔ first x.val = 0 := by
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
    change polynomial x.val = south.val
    simp only [polynomial, hx, map_zero, zero_sub, zero_mul, smul_zero, hb]
    exact south_join

def southAxis : V 4 →ₗᵢ[ℝ] V 8 where
  toLinearMap := planeCoordinates.toLinearMap.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ).symm.toLinearMap.comp
      (LinearMap.inr ℝ ℍ ℍ)).comp Quaternion.linearIsometryEquivTuple.symm.toLinearMap)
  norm_map' v := by
    change ‖planeCoordinates (WithLp.toLp 2
      ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm v))‖ = ‖v‖
    rw [planeCoordinates.norm_map, WithLp.norm_toLp_snd,
      Quaternion.linearIsometryEquivTuple.symm.norm_map]

theorem first_southAxis (v : V 4) : first (southAxis v) = 0 := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm v)))).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_southAxis (v : V 4) :
    second (southAxis v) = Quaternion.linearIsometryEquivTuple.symm v := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm v)))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem southAxis_second_of_first_eq_zero (x : V 8) (hx : first x = 0) :
    southAxis (Quaternion.linearIsometryEquivTuple (second x)) = x := by
  change planeCoordinates (WithLp.toLp 2 ((0 : ℍ), Quaternion.linearIsometryEquivTuple.symm
    (Quaternion.linearIsometryEquivTuple (second x)))) = x
  rw [LinearIsometryEquiv.symm_apply_apply, ← hx]
  exact planeCoordinates.apply_symm_apply x

theorem southAxis_mem_sphere (q : Sphere 3) : southAxis q.val ∈ Sphere 7 := by
  rw [mem_sphere_zero_iff_norm, southAxis.norm_map]
  exact mem_sphere_zero_iff_norm.mp q.property

def southFiberPoint : C(Sphere 3, Sphere 7) :=
  ⟨fun q ↦ ⟨southAxis q.val, southAxis_mem_sphere q⟩,
    (southAxis.continuous.comp continuous_subtype_val).subtype_mk southAxis_mem_sphere⟩

theorem first_southFiberPoint (q : Sphere 3) : first (southFiberPoint q).val = 0 :=
  first_southAxis q.val

theorem second_southFiberPoint (q : Sphere 3) :
    second (southFiberPoint q).val = Quaternion.linearIsometryEquivTuple.symm q.val :=
  second_southAxis q.val

theorem sphereMap_southFiberPoint (q : Sphere 3) : sphereMap (southFiberPoint q) = south :=
  (sphereMap_eq_south_iff _).mpr (first_southFiberPoint q)

theorem contMDiff_southFiberPoint : ContMDiff (𝓡 3) (𝓡 7) ∞ southFiberPoint := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (southAxis.toContinuousLinearMap.contDiff.contMDiff.comp
    contMDiff_coe_sphere).codRestrict_sphere (fun q ↦ (southFiberPoint q).property)

def southFiberInverse (x : {x : Sphere 7 // sphereMap x = south}) : Sphere 3 :=
  ⟨Quaternion.linearIsometryEquivTuple (second x.val.val), by
    rw [mem_sphere_zero_iff_norm, Quaternion.linearIsometryEquivTuple.norm_map]
    have hs := normSq_sum x.val.val
    rw [(sphereMap_eq_south_iff x.val).mp x.property, map_zero, zero_add,
      mem_sphere_zero_iff_norm.mp x.val.property, one_pow] at hs
    rw [Quaternion.normSq_eq_norm_mul_self] at hs
    nlinarith [norm_nonneg (second x.val.val)]⟩

theorem southFiberInverse_southFiberPoint (q : Sphere 3) :
    southFiberInverse ⟨southFiberPoint q, sphereMap_southFiberPoint q⟩ = q := by
  apply Subtype.ext
  change Quaternion.linearIsometryEquivTuple (second (southFiberPoint q).val) = q.val
  rw [second_southFiberPoint, LinearIsometryEquiv.apply_symm_apply]

theorem southFiberPoint_southFiberInverse (x : {x : Sphere 7 // sphereMap x = south}) :
    southFiberPoint (southFiberInverse x) = x.val := by
  apply Subtype.ext
  exact southAxis_second_of_first_eq_zero x.val.val ((sphereMap_eq_south_iff x.val).mp x.property)

def southFiberHomeomorph : Sphere 3 ≃ₜ {x : Sphere 7 // sphereMap x = south} where
  toFun q := ⟨southFiberPoint q, sphereMap_southFiberPoint q⟩
  invFun := southFiberInverse
  left_inv := southFiberInverse_southFiberPoint
  right_inv x := Subtype.ext (southFiberPoint_southFiberInverse x)
  continuous_toFun := southFiberPoint.continuous.subtype_mk _
  continuous_invFun := (Quaternion.linearIsometryEquivTuple.continuous.comp
    (second.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

end NoExoticSixSphere.QuaternionicHopf
