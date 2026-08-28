import Wikipedia.NoExoticSixSphere.QuaternionicHopfProjectionAlgebra

/-!
# The continuous projection-operator family over the actual four-sphere

The operator acts on the original Euclidean eight-space through the
quaternionic coordinate isometry. Its image equations identify the
Hopf image of every unit vector in that image.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def pairCoordinates : (ℍ × ℍ) ≃L[ℝ] V 8 :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℍ ℍ).symm.trans
    planeCoordinates.toContinuousLinearEquiv

def tailQuaternion : V 5 →L[ℝ] ℍ :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap.comp (SphereCylinder.tail 3)

theorem tailQuaternion_join (t : ℝ) (z : ℍ) :
    tailQuaternion (SphereCylinder.join 3 (t, Quaternion.linearIsometryEquivTuple z)) = z := by
  change Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3
    (SphereCylinder.join 3 (t, Quaternion.linearIsometryEquivTuple z))) = z
  rw [SphereCylinder.tail_join, LinearIsometryEquiv.symm_apply_apply]

def projectionOperator (y : V 5) : V 8 →L[ℝ] V 8 :=
  pairCoordinates.toContinuousLinearMap.comp
    (((1 + y 0) • first + (ContinuousLinearMap.mul ℝ ℍ (tailQuaternion y)).comp second).prod
      ((ContinuousLinearMap.mul ℝ ℍ (star (tailQuaternion y))).comp first +
        (1 - y 0) • second))

theorem first_projectionOperator (y : V 5) (x : V 8) :
    first (projectionOperator y x) =
      projectedFirst (y 0) (tailQuaternion y) (first x) (second x) := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2 (_,
    (star (tailQuaternion y) * first x + (1 - y 0) • second x))))).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem second_projectionOperator (y : V 5) (x : V 8) :
    second (projectionOperator y x) =
      projectedSecond (y 0) (tailQuaternion y) (first x) (second x) := by
  change (planeCoordinates.symm (planeCoordinates (WithLp.toLp 2
    ((1 + y 0) • first x + tailQuaternion y * second x, _)))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem first_second_ext {x w : V 8} (h₁ : first x = first w) (h₂ : second x = second w) :
    x = w := by
  apply planeCoordinates.symm.injective
  apply WithLp.ofLp_injective 2
  exact Prod.ext h₁ h₂

theorem sphere_coordinate_norm (y : Sphere 4) :
    y.val 0 ^ 2 + Quaternion.normSq (tailQuaternion y.val) = 1 := by
  have h := SphereCylinder.norm_join_sq 3 (y.val 0) (SphereCylinder.tail 3 y.val)
  have he : SphereCylinder.join 3 (y.val 0, SphereCylinder.tail 3 y.val) = y.val :=
    (SphereCylinder.join 3).apply_symm_apply y.val
  rw [he, mem_sphere_zero_iff_norm.mp y.property, one_pow] at h
  have ht : ‖tailQuaternion y.val‖ = ‖SphereCylinder.tail 3 y.val‖ :=
    Quaternion.linearIsometryEquivTuple.symm.norm_map _
  rw [← ht, norm_sq_eq_normSq] at h
  exact h.symm

theorem polynomial_of_eigen (x : Sphere 7) (y : Sphere 4)
    (h₁ : (1 - y.val 0) • first x.val = tailQuaternion y.val * second x.val)
    (h₂ : (1 + y.val 0) • second x.val = star (tailQuaternion y.val) * first x.val) :
    sphereMap x = y := by
  have hn := normSq_sum x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow] at hn
  apply Subtype.ext
  change polynomial x.val = y.val
  rw [polynomial, eigen_head _ _ _ _ h₁ h₂ hn, eigen_tail _ _ _ _ h₁ h₂ hn]
  change SphereCylinder.join 3 (y.val 0, Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 y.val))) = y.val
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (SphereCylinder.join 3).apply_symm_apply y.val

theorem projectionOperator_self (x : Sphere 7) :
    projectionOperator (sphereMap x).val x.val = (2 : ℝ) • x.val := by
  have hn := normSq_sum x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow] at hn
  apply first_second_ext
  · rw [first_projectionOperator, map_smul]
    change projectedFirst (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val))
      (tailQuaternion (polynomial x.val)) (first x.val) (second x.val) = _
    rw [polynomial, tailQuaternion_join]
    exact projectedFirst_self _ _ hn
  · rw [second_projectionOperator, map_smul]
    change projectedSecond (Quaternion.normSq (first x.val) - Quaternion.normSq (second x.val))
      (tailQuaternion (polynomial x.val)) (first x.val) (second x.val) = _
    rw [polynomial, tailQuaternion_join]
    exact projectedSecond_self _ _ hn

theorem projectionOperator_image_first (y : Sphere 4) (x : V 8) :
    (1 - y.val 0) • first (projectionOperator y.val x) =
      tailQuaternion y.val * second (projectionOperator y.val x) := by
  rw [first_projectionOperator, second_projectionOperator]
  exact projectedFirst_relation _ _ _ _ (sphere_coordinate_norm y)

theorem projectionOperator_image_second (y : Sphere 4) (x : V 8) :
    (1 + y.val 0) • second (projectionOperator y.val x) =
      star (tailQuaternion y.val) * first (projectionOperator y.val x) := by
  rw [first_projectionOperator, second_projectionOperator]
  exact projectedSecond_relation _ _ _ _ (sphere_coordinate_norm y)

theorem continuous_projectionOperator : Continuous projectionOperator := by
  unfold projectionOperator
  apply continuous_const.clm_comp
  change Continuous (fun y : V 5 ↦
    (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := V 8) (F := ℍ) (G := ℍ) ℝ)
    (((1 + y 0) • first + (ContinuousLinearMap.mul ℝ ℍ (tailQuaternion y)).comp second),
      (ContinuousLinearMap.mul ℝ ℍ (star (tailQuaternion y))).comp first +
        (1 - y 0) • second))
  apply (ContinuousLinearMap.prodL (𝕜 := ℝ) (E := V 8) (F := ℍ) (G := ℍ) ℝ).continuous.comp
  apply Continuous.prodMk
  · exact ((continuous_const.add (EuclideanSpace.proj 0).continuous).smul continuous_const).add
      (((ContinuousLinearMap.mul ℝ ℍ).continuous.comp tailQuaternion.continuous).clm_comp
        continuous_const)
  · exact (((ContinuousLinearMap.mul ℝ ℍ).continuous.comp
      (conjugation.continuous.comp tailQuaternion.continuous)).clm_comp continuous_const).add
      ((continuous_const.sub (EuclideanSpace.proj 0).continuous).smul continuous_const)

end NoExoticSixSphere.QuaternionicHopf
