import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthDifferential
import Wikipedia.NoExoticSixSphere.QuaternionicHopfProjectionOperator
import Wikipedia.NoExoticSixSphere.CanonicalRightInverse

/-!
# Explicit ambient normal equations along the south Hopf fiber

The equations are the source unit-norm equation and the quaternion tail
of the actual Hopf polynomial. Their differential has an explicit
orthogonal right inverse with quaternion twist given by right multiplication.
These equations have both pole fibers as zeros; they isolate the south
fiber only after restricting to the appropriate hemisphere.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

abbrev SouthNormalModel := WithLp 2 (ℝ × ℍ)

def southNormalEquations (x : V 8) : SouthNormalModel :=
  WithLp.toLp 2 (‖x‖ ^ 2 - 1, tailQuaternion (polynomial x))

theorem contDiff_southNormalEquations : ContDiff ℝ ∞ southNormalEquations :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ).symm.contDiff.comp
    (((contDiff_norm_sq ℝ).sub contDiff_const).prodMk
      (tailQuaternion.contDiff.comp contDiff_polynomial))

theorem southNormalEquations_zero (x : Sphere 7) (hx : first x.val = 0) :
    southNormalEquations x.val = 0 := by
  change WithLp.toLp 2 (‖x.val‖ ^ 2 - 1, tailQuaternion (polynomial x.val)) = 0
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow, sub_self,
    polynomial, tailQuaternion_join, hx, zero_mul, smul_zero]
  rfl

theorem southNormalEquations_fderiv (x : V 8) (hx : first x = 0) (v : V 8) :
    fderiv ℝ southNormalEquations x v = WithLp.toLp 2
      (2 * inner ℝ x v, (2 : ℝ) • (first v * star (second x))) := by
  have h₁ := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1
  have h₂ := tailQuaternion.hasFDerivAt.comp x
    (contDiff_polynomial.differentiable (by simp) x).hasFDerivAt
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ).symm.hasFDerivAt.comp x
    (h₁.prodMk h₂)
  change HasFDerivAt (𝕜 := ℝ) southNormalEquations _ x at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
  rw [polynomial_fderiv_south x hx, tailQuaternion_join]
  rfl

theorem inner_quaternion_coordinates (x y : V 8) :
    inner ℝ x y = inner ℝ (first x) (first y) + inner ℝ (second x) (second y) := by
  rw [← planeCoordinates.symm.inner_map_map, WithLp.prod_inner_apply]
  rfl

def southNormalLift (b : ℍ) : SouthNormalModel →L[ℝ] V 8 :=
  (1 / 2 : ℝ) •
    (firstAxis.comp (((ContinuousLinearMap.mul ℝ ℍ).flip b).comp
      (WithLp.sndL 2 ℝ ℝ ℍ)) +
    secondAxis.comp ((ContinuousLinearMap.toSpanSingleton ℝ b).comp
      (WithLp.fstL 2 ℝ ℝ ℍ)))

theorem first_southNormalLift (b : ℍ) (p : SouthNormalModel) :
    first (southNormalLift b p) = (1 / 2 : ℝ) • (p.snd * b) := by
  change first ((1 / 2 : ℝ) • (firstAxis (p.snd * b) + secondAxis (p.fst • b))) = _
  rw [map_smul, map_add, first_firstAxis, first_secondAxis, add_zero]

theorem second_southNormalLift (b : ℍ) (p : SouthNormalModel) :
    second (southNormalLift b p) = (1 / 2 : ℝ) • (p.fst • b) := by
  change second ((1 / 2 : ℝ) • (firstAxis (p.snd * b) + secondAxis (p.fst • b))) = _
  rw [map_smul, map_add, second_firstAxis, second_secondAxis, zero_add]

theorem second_norm_sq_south (x : Sphere 7) (hx : first x.val = 0) : ‖second x.val‖ ^ 2 = 1 := by
  have h := normSq_sum x.val
  rw [hx, map_zero, zero_add, mem_sphere_zero_iff_norm.mp x.property, one_pow] at h
  rwa [norm_sq_eq_normSq]

theorem southNormalLift_right_inverse (x : Sphere 7) (hx : first x.val = 0)
    (p : SouthNormalModel) :
    fderiv ℝ southNormalEquations x.val (southNormalLift (second x.val) p) = p := by
  rw [southNormalEquations_fderiv x.val hx]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change 2 * inner ℝ x.val (southNormalLift (second x.val) p) = p.fst
    rw [inner_quaternion_coordinates, hx, inner_zero_left, zero_add, second_southNormalLift,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      second_norm_sq_south x hx]
    ring
  · change (2 : ℝ) • (first (southNormalLift (second x.val) p) * star (second x.val)) = p.snd
    rw [first_southNormalLift]
    exact south_transverse_right_inverse _ _ (south_second_mul_star x hx)

theorem southNormalEquations_surjective (x : Sphere 7) (hx : first x.val = 0) :
    Function.Surjective (fderiv ℝ southNormalEquations x.val) :=
  fun p ↦ ⟨southNormalLift (second x.val) p, southNormalLift_right_inverse x hx p⟩

theorem southNormalEquations_kernel (x : Sphere 7) (hx : first x.val = 0) (v : V 8) :
    fderiv ℝ southNormalEquations x.val v = 0 ↔
      first v = 0 ∧ inner ℝ (second x.val) (second v) = 0 := by
  rw [southNormalEquations_fderiv x.val hx]
  constructor
  · intro hv
    have h₁ := congrArg (fun p : SouthNormalModel ↦ p.fst) hv
    have h₂ := congrArg (fun p : SouthNormalModel ↦ p.snd) hv
    change 2 * inner ℝ x.val v = 0 at h₁
    change (2 : ℝ) • (first v * star (second x.val)) = 0 at h₂
    have hb : second x.val ≠ 0 := by
      have h := south_second_mul_star x hx
      intro hz
      simp only [hz, zero_mul, zero_ne_one] at h
    have hv₁ : first v = 0 := by
      have ht : first v * star (second x.val) = 0 :=
        (smul_eq_zero.mp h₂).resolve_left (by norm_num)
      exact (mul_eq_zero.mp ht).resolve_right (star_ne_zero.mpr hb)
    refine ⟨hv₁, ?_⟩
    rw [inner_quaternion_coordinates, hx, inner_zero_left, zero_add] at h₁
    linarith
  · rintro ⟨hv, hi⟩
    rw [inner_quaternion_coordinates, hx, inner_zero_left, zero_add, hi, mul_zero,
      hv, zero_mul, smul_zero]
    rfl

theorem southNormalLift_mem_orthogonal (x : Sphere 7) (hx : first x.val = 0)
    (p : SouthNormalModel) :
    southNormalLift (second x.val) p ∈ (fderiv ℝ southNormalEquations x.val).kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  obtain ⟨h₁, h₂⟩ := (southNormalEquations_kernel x hx v).mp hv
  rw [inner_quaternion_coordinates, h₁, inner_zero_right, zero_add, second_southNormalLift,
    real_inner_smul_left, real_inner_smul_left, h₂]
  simp

theorem southNormalEquations_orthogonalRightInverse (x : Sphere 7) (hx : first x.val = 0) :
    orthogonalRightInverse (fderiv ℝ southNormalEquations x.val) = southNormalLift (second x.val) :=
  orthogonalRightInverse_eq_of_rightInverse _ (southNormalEquations_surjective x hx) _
    (southNormalLift_right_inverse x hx)
    (fun _ ⟨p, hp⟩ ↦ hp ▸ southNormalLift_mem_orthogonal x hx p)

end NoExoticSixSphere.QuaternionicHopf
