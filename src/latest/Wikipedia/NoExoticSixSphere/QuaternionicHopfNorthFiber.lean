import Wikipedia.NoExoticSixSphere.QuaternionicHopfPolynomial
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# The actual north fiber of the smooth quaternionic Hopf map

The fiber over the standard four-sphere pole is exactly the first
quaternionic axis. The displayed map from the standard three-sphere
is smooth, and its explicit inverse identifies the actual fiber as a
topological space. A regular-fiber atlas and its induced framing are
not supplied by this identification alone.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def axis : V 4 →ₗᵢ[ℝ] V 8 where
  toLinearMap := planeCoordinates.toLinearMap.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ).symm.toLinearMap.comp
      (LinearMap.inl ℝ ℍ ℍ)).comp Quaternion.linearIsometryEquivTuple.symm.toLinearMap)
  norm_map' v := by
    change ‖planeCoordinates (WithLp.toLp 2
      (Quaternion.linearIsometryEquivTuple.symm v, (0 : ℍ)))‖ = ‖v‖
    rw [planeCoordinates.norm_map, WithLp.norm_toLp_fst,
      Quaternion.linearIsometryEquivTuple.symm.norm_map]

theorem first_axis (v : V 4) : first (axis v) = Quaternion.linearIsometryEquivTuple.symm v := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    (Quaternion.linearIsometryEquivTuple.symm v, (0 : ℍ))))).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_axis (v : V 4) : second (axis v) = 0 := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    (Quaternion.linearIsometryEquivTuple.symm v, (0 : ℍ))))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem axis_first_of_second_eq_zero (x : V 8) (hx : second x = 0) :
    axis (Quaternion.linearIsometryEquivTuple (first x)) = x := by
  change planeCoordinates (WithLp.toLp 2
    (Quaternion.linearIsometryEquivTuple.symm (Quaternion.linearIsometryEquivTuple (first x)),
      (0 : ℍ))) = x
  rw [LinearIsometryEquiv.symm_apply_apply, ← hx]
  exact planeCoordinates.apply_symm_apply x

theorem pole_join : SphereCylinder.join 3 (1, (0 : V 4)) = (spherePole 4).val := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [spherePole]
  · simp [spherePole, Fin.succ_ne_zero]

theorem sphereMap_eq_pole_iff (x : Sphere 7) : sphereMap x = spherePole 4 ↔ second x.val = 0 := by
  have hs := normSq_sum x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow] at hs
  constructor
  · intro hx
    have hh := congrArg (fun y : Sphere 4 ↦ y.val 0) hx
    change Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val) = 1 at hh
    apply Quaternion.normSq_eq_zero.mp
    linarith
  · intro hx
    have ha : Quaternion.normSq (first x.val) = 1 := by simpa only [hx, map_zero, add_zero] using hs
    apply Subtype.ext
    change SphereCylinder.join 3
      (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val),
        Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (first x.val * star (second x.val)))) = _
    simp only [ha, hx, map_zero, sub_zero, star_zero, mul_zero, smul_zero]
    exact pole_join

theorem axis_mem_sphere (q : Sphere 3) : axis q.val ∈ Sphere 7 := by
  rw [mem_sphere_zero_iff_norm, axis.norm_map]
  exact mem_sphere_zero_iff_norm.mp q.property

def fiberPoint : C(Sphere 3, Sphere 7) :=
  ⟨fun q ↦ ⟨axis q.val, axis_mem_sphere q⟩,
    (axis.continuous.comp continuous_subtype_val).subtype_mk axis_mem_sphere⟩

theorem first_fiberPoint (q : Sphere 3) :
    first (fiberPoint q).val = Quaternion.linearIsometryEquivTuple.symm q.val := first_axis q.val

theorem second_fiberPoint (q : Sphere 3) : second (fiberPoint q).val = 0 := second_axis q.val

theorem sphereMap_fiberPoint (q : Sphere 3) : sphereMap (fiberPoint q) = spherePole 4 :=
  (sphereMap_eq_pole_iff _).mpr (second_fiberPoint q)

theorem contMDiff_fiberPoint : ContMDiff (𝓡 3) (𝓡 7) ∞ fiberPoint := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (axis.toContinuousLinearMap.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
    (fun q ↦ (fiberPoint q).property)

def fiberInverse (x : {x : Sphere 7 // sphereMap x = spherePole 4}) : Sphere 3 :=
  ⟨Quaternion.linearIsometryEquivTuple (first x.val.val), by
    rw [mem_sphere_zero_iff_norm, Quaternion.linearIsometryEquivTuple.norm_map]
    have hs := normSq_sum x.val.val
    rw [(sphereMap_eq_pole_iff x.val).mp x.property, map_zero, add_zero,
      mem_sphere_zero_iff_norm.mp x.val.property, one_pow] at hs
    rw [Quaternion.normSq_eq_norm_mul_self] at hs
    nlinarith [norm_nonneg (first x.val.val)]⟩

theorem fiberInverse_fiberPoint (q : Sphere 3) :
    fiberInverse ⟨fiberPoint q, sphereMap_fiberPoint q⟩ = q := by
  apply Subtype.ext
  change Quaternion.linearIsometryEquivTuple (first (fiberPoint q).val) = q.val
  rw [first_fiberPoint, LinearIsometryEquiv.apply_symm_apply]

theorem fiberPoint_fiberInverse (x : {x : Sphere 7 // sphereMap x = spherePole 4}) :
    fiberPoint (fiberInverse x) = x.val := by
  apply Subtype.ext
  exact axis_first_of_second_eq_zero x.val.val ((sphereMap_eq_pole_iff x.val).mp x.property)

def fiberHomeomorph : Sphere 3 ≃ₜ {x : Sphere 7 // sphereMap x = spherePole 4} where
  toFun q := ⟨fiberPoint q, sphereMap_fiberPoint q⟩
  invFun := fiberInverse
  left_inv := fiberInverse_fiberPoint
  right_inv x := Subtype.ext (fiberPoint_fiberInverse x)
  continuous_toFun := fiberPoint.continuous.subtype_mk _
  continuous_invFun := (Quaternion.linearIsometryEquivTuple.continuous.comp
    (first.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

end NoExoticSixSphere.QuaternionicHopf
