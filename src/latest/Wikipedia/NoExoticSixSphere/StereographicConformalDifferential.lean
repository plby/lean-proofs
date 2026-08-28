import Wikipedia.NoExoticSixSphere.StereographicReflectionCoordinates

/-!
# The actual inverse stereographic derivative as a scaled reflection

Differentiate the original finite compactification formula at every
Euclidean point. The derivative is the original pole-complement inclusion
followed by the global reflection, with positive factor `4 / (norm² + 4)`.
In particular it preserves orthogonality up to that same scalar factor.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.StereographicEquator

def finiteScale (n : ℕ) (x : V n) : ℝ := 4 * (‖x‖ ^ 2 + 4)⁻¹

theorem finiteScale_pos (n : ℕ) (x : V n) : 0 < finiteScale n x := by
  unfold finiteScale
  positivity

theorem continuous_finiteScale (n : ℕ) : Continuous (finiteScale n) := by
  change Continuous (fun x : V n ↦ (4 : ℝ) * (‖x‖ ^ 2 + 4)⁻¹)
  have hden : Continuous (fun x : V n ↦ ‖x‖ ^ 2 + (4 : ℝ)) :=
    (continuous_id.norm.pow 2).add continuous_const
  exact continuous_const.mul (hden.inv₀ (fun x ↦ by positivity))

theorem fderiv_finiteAmbient_reflection (n : ℕ) (x : V n) :
    fderiv ℝ (finiteAmbient n) x =
      finiteScale n x • ((finiteReflection n x).toContinuousLinearMap.comp (liftL n)) := by
  have hN := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hI := (hasFDerivAt_inv hd).comp x (hN.add_const 4)
  have hA := ((liftL n).hasFDerivAt.const_smul (4 : ℝ)).add
    ((hN.sub_const 4).smul_const (spherePole n).val)
  have h := hI.smul hA
  change HasFDerivAt (fun y : V n ↦ (‖y‖ ^ 2 + 4)⁻¹ •
    ((4 : ℝ) • liftL n y + (‖y‖ ^ 2 - 4) • (spherePole n).val)) _ x at h
  have he : finiteAmbient n = (fun y : V n ↦ (‖y‖ ^ 2 + 4)⁻¹ •
      ((4 : ℝ) • liftL n y + (‖y‖ ^ 2 - 4) • (spherePole n).val)) := by
    funext y
    rw [finiteAmbient, finite_apply, liftL_apply, smul_add]
  rw [he, h.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp only [finiteScale, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, innerSL_apply_apply,
    Function.comp_apply, Pi.add_apply, Pi.smul_apply, finiteReflection_operator,
    liftL_apply, hyperplaneReflectionOperator_apply]
  rw [reflectionNormal_norm_sq, reflectionNormal_inner_lift, reflectionNormal]
  simp only [← inv_pow]
  match_scalars <;> ring_nf
  field_simp [show (4 : ℝ) + ‖x‖ ^ 2 ≠ 0 by positivity]
  ring

theorem fderiv_finiteAmbient_apply (n : ℕ) (x w : V n) :
    fderiv ℝ (finiteAmbient n) x w = finiteScale n x • finiteReflection n x (lift n w) := by
  rw [fderiv_finiteAmbient_reflection]
  rfl

theorem inner_fderiv_finiteAmbient (n : ℕ) (x v w : V n) :
    inner ℝ (fderiv ℝ (finiteAmbient n) x v) (fderiv ℝ (finiteAmbient n) x w) =
      finiteScale n x ^ 2 * inner ℝ v w := by
  rw [fderiv_finiteAmbient_apply, fderiv_finiteAmbient_apply,
    real_inner_smul_left, real_inner_smul_right,
    (finiteReflection n x).inner_map_map, inner_lift]
  ring

theorem inner_finiteAmbient_fderiv (n : ℕ) (x w : V n) :
    inner ℝ (finiteAmbient n x) (fderiv ℝ (finiteAmbient n) x w) = 0 := by
  rw [fderiv_finiteAmbient_apply, ← finiteReflection_pole, real_inner_smul_right,
    (finiteReflection n x).inner_map_map, real_inner_comm, inner_lift_pole, mul_zero]

end NoExoticSixSphere.StereographicEquator
