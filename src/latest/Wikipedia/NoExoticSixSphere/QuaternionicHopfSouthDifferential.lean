import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthFiber
import Wikipedia.NoExoticSixSphere.QuaternionicHopfRegularFiber

/-!
# The exact differential and regularity of the nonbasepoint Hopf fiber

At `(0,b)` the quaternion component has differential `w -> 2 w conjugate(b)`
in the first quaternion direction. Its explicit right inverse lies in the
original sphere tangent space. This proves that the south pole is a regular value.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def firstAxis : ℍ →L[ℝ] V 8 :=
  axis.toContinuousLinearMap.comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap

theorem first_firstAxis (w : ℍ) : first (firstAxis w) = w := by
  change first (axis (Quaternion.linearIsometryEquivTuple w)) = w
  rw [first_axis, LinearIsometryEquiv.symm_apply_apply]

theorem second_firstAxis (w : ℍ) : second (firstAxis w) = 0 :=
  second_axis (Quaternion.linearIsometryEquivTuple w)

theorem polynomial_fderiv_south (x : V 8) (hx : first x = 0) (v : V 8) :
    fderiv ℝ polynomial x v = SphereCylinder.join 3
      (-2 * inner ℝ (second x) (second v),
        Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (first v * star (second x)))) := by
  have h₁ := (hasStrictFDerivAt_norm_sq (first x)).hasFDerivAt.comp x first.hasFDerivAt
  have h₂ := (hasStrictFDerivAt_norm_sq (second x)).hasFDerivAt.comp x second.hasFDerivAt
  have hmul := first.hasFDerivAt.mul' (conjugation.hasFDerivAt.comp x second.hasFDerivAt)
  have htail := Quaternion.linearIsometryEquivTuple.hasFDerivAt.comp x
    ((hasFDerivAt_const (2 : ℝ) x).smul hmul)
  have h := (SphereCylinder.join 3).hasFDerivAt.comp x ((h₁.sub h₂).prodMk htail)
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, norm_sq_eq_normSq] at h
  change HasFDerivAt (𝕜 := ℝ) polynomial _ x at h
  rw [h.fderiv]
  simp [hx, conjugation]

theorem polynomial_fderiv_first (x : V 8) (hx : first x = 0) (w : ℍ) :
    fderiv ℝ polynomial x (firstAxis w) = SphereCylinder.join 3
      (0, Quaternion.linearIsometryEquivTuple ((2 : ℝ) • (w * star (second x)))) := by
  rw [polynomial_fderiv_south x hx, first_firstAxis, second_firstAxis,
    inner_zero_right, mul_zero]

theorem inner_firstAxis (x : V 8) (hx : first x = 0) (w : ℍ) :
    inner ℝ x (firstAxis w) = 0 := by
  have he : x = planeCoordinates (WithLp.toLp 2 ((0 : ℍ), second x)) := by
    rw [← hx]
    exact (planeCoordinates.apply_symm_apply x).symm
  rw [he]
  change inner ℝ (planeCoordinates (WithLp.toLp 2 ((0 : ℍ), second x)))
    (planeCoordinates (WithLp.toLp 2 (w, (0 : ℍ)))) = 0
  rw [planeCoordinates.inner_map_map]
  simp

theorem south_second_mul_star (x : Sphere 7) (hx : first x.val = 0) :
    second x.val * star (second x.val) = 1 := by
  have hs := normSq_sum x.val
  rw [hx, map_zero, zero_add, mem_sphere_zero_iff_norm.mp x.property, one_pow] at hs
  rw [Quaternion.self_mul_star, hs]
  rfl

theorem south_transverse_right_inverse (b w : ℍ) (hb : b * star b = 1) :
    (2 : ℝ) • (((1 / 2 : ℝ) • (w * b)) * star b) = w := by
  rw [smul_mul_assoc, mul_assoc, hb, mul_one, smul_smul]
  norm_num

theorem south_inner_head (z : V 5) : inner ℝ south.val z = -(z 0) := by
  change inner ℝ (-(spherePole 4).val) z = -(z 0)
  rw [inner_neg_left, pole_inner_head]

theorem polynomial_south_tangent_surjective (x : Sphere 7) (hx : first x.val = 0)
    (z : V 5) (hz : z 0 = 0) :
    ∃ v : V 8, inner ℝ x.val v = 0 ∧ fderiv ℝ polynomial x.val v = z := by
  let w := Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 z)
  let v := (1 / 2 : ℝ) • (w * second x.val)
  refine ⟨firstAxis v, inner_firstAxis x.val hx v, ?_⟩
  rw [polynomial_fderiv_first x.val hx]
  have ht := south_transverse_right_inverse (second x.val) w (south_second_mul_star x hx)
  change (2 : ℝ) • (v * star (second x.val)) = w at ht
  rw [ht]
  change SphereCylinder.join 3 (0, Quaternion.linearIsometryEquivTuple
    (Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.tail 3 z))) = z
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact join_zero_tail z hz

theorem south_regular (x : Sphere 7) (hx : sphereMap x = south) :
    Function.Surjective (mfderiv (𝓡 7) (𝓡 4) sphereMap x) := by
  apply sphereMap_mfderiv_surjective_of_ambient polynomial sphereMap contDiff_polynomial
    contMDiff_sphereMap sphereMap_val x
  intro z hz
  rw [hx, south_inner_head, neg_eq_zero] at hz
  exact polynomial_south_tangent_surjective x ((sphereMap_eq_south_iff x).mp hx) z hz

end NoExoticSixSphere.QuaternionicHopf
