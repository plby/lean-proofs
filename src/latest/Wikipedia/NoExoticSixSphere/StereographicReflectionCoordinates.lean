import Wikipedia.NoExoticSixSphere.StereographicStabilizedCoordinates
import Wikipedia.NoExoticSixSphere.OrthogonalRotations

/-!
# A global reflection family for the actual inverse stereographic chart

Mathlib's finite coordinates have scale two. Reflection perpendicular to
`2 * pole - lift x` sends the original pole to the actual compactification
point. This normal never vanishes, so the family and its inverse are
continuous over the whole original Euclidean coordinate space.
-/

noncomputable section

namespace NoExoticSixSphere.StereographicEquator

def reflectionNormal (n : ℕ) (x : V n) : V (n + 1) :=
  (2 : ℝ) • (spherePole n).val - lift n x

theorem reflectionNormal_norm_sq (n : ℕ) (x : V n) :
    ‖reflectionNormal n x‖ ^ 2 = ‖x‖ ^ 2 + 4 := by
  have hp : inner ℝ (spherePole n).val (lift n x) = 0 := by
    rw [real_inner_comm]
    exact inner_lift_pole n x
  rw [reflectionNormal, norm_sub_sq_real, norm_smul, ClosedHemisphere.unit_norm,
    norm_lift, real_inner_smul_left, hp]
  norm_num
  ring

theorem reflectionNormal_inner_pole (n : ℕ) (x : V n) :
    inner ℝ (reflectionNormal n x) (spherePole n).val = 2 := by
  rw [reflectionNormal, inner_sub_left, real_inner_smul_left, inner_lift_pole,
    real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm]
  norm_num

theorem reflectionNormal_inner_lift (n : ℕ) (x w : V n) :
    inner ℝ (reflectionNormal n x) (lift n w) = -inner ℝ x w := by
  have hp : inner ℝ (spherePole n).val (lift n w) = 0 := by
    rw [real_inner_comm]
    exact inner_lift_pole n w
  rw [reflectionNormal, inner_sub_left, real_inner_smul_left, hp, inner_lift,
    mul_zero, zero_sub]

theorem reflectionNormal_ne_zero (n : ℕ) (x : V n) : reflectionNormal n x ≠ 0 := by
  intro h
  have he := reflectionNormal_inner_pole n x
  rw [h, inner_zero_left] at he
  norm_num at he

theorem continuous_reflectionNormal (n : ℕ) : Continuous (reflectionNormal n) :=
  continuous_const.sub (liftL n).continuous

def finiteReflection (n : ℕ) (x : V n) : V (n + 1) ≃ₗᵢ[ℝ] V (n + 1) :=
  (ℝ ∙ reflectionNormal n x)ᗮ.reflection

theorem finiteReflection_operator (n : ℕ) (x : V n) :
    (finiteReflection n x).toContinuousLinearMap =
      hyperplaneReflectionOperator (reflectionNormal n x) := rfl

theorem continuous_finiteReflection (n : ℕ) :
    Continuous (fun x ↦ (finiteReflection n x).toContinuousLinearMap) :=
  continuous_hyperplaneReflectionOperator (reflectionNormal n)
    (continuous_reflectionNormal n) (reflectionNormal_ne_zero n)

theorem finiteReflection_symm (n : ℕ) (x : V n) :
    (finiteReflection n x).symm = finiteReflection n x :=
  Submodule.reflection_symm

theorem finiteReflection_pole (n : ℕ) (x : V n) :
    finiteReflection n x (spherePole n).val = finiteAmbient n x := by
  change hyperplaneReflectionOperator (reflectionNormal n x) (spherePole n).val = _
  rw [hyperplaneReflectionOperator_apply, reflectionNormal_norm_sq, reflectionNormal_inner_pole,
    finiteAmbient, finite_apply, reflectionNormal]
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hc : 1 - (2 * (‖x‖ ^ 2 + 4)⁻¹ * 2) * 2 =
      (‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4) := by
    field_simp [hd]
    ring
  calc
    _ = (1 - (2 * (‖x‖ ^ 2 + 4)⁻¹ * 2) * 2) • (spherePole n).val +
        (2 * (‖x‖ ^ 2 + 4)⁻¹ * 2) • lift n x := by module
    _ = _ := by rw [hc]; module

end NoExoticSixSphere.StereographicEquator
