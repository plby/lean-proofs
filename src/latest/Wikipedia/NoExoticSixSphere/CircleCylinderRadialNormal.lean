import Wikipedia.NoExoticSixSphere.CircleCylinderClock
import Wikipedia.NoExoticSixSphere.CanonicalRightInverse

/-!
# The actual circle equation's canonical radial normal

For a unit circle point the differential of `‖v‖² - 1` has canonical
orthogonal right inverse `t ↦ (t/2) c`. This retains the genuine signed
radial vector and its scale, not just the normal line.
-/

noncomputable section

open Function
open scoped ContDiff InnerProductSpace

namespace NoExoticSixSphere.CircleCylinder

def circleNorm (v : V) : ℝ := ‖v‖ ^ 2 - 1

theorem contDiff_circleNorm : ContDiff ℝ ∞ circleNorm :=
  (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const

theorem fderiv_circleNorm (c : Sphere 1) :
    fderiv ℝ circleNorm c.val = 2 • innerSL ℝ c.val :=
  ((hasStrictFDerivAt_norm_sq c.val).hasFDerivAt.sub_const 1).fderiv

def circleNormal (c : Sphere 1) : ℝ →L[ℝ] V :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight ((1 / 2 : ℝ) • c.val)

theorem circleNormal_apply (c : Sphere 1) (t : ℝ) : circleNormal c t = (t / 2) • c.val := by
  change t • ((1 / 2 : ℝ) • c.val) = (t / 2) • c.val
  rw [smul_smul, mul_one_div]

theorem circleNorm_rightInverse (c : Sphere 1) (t : ℝ) :
    fderiv ℝ circleNorm c.val (circleNormal c t) = t := by
  rw [fderiv_circleNorm, circleNormal_apply, two_smul]
  change inner ℝ c.val ((t / 2) • c.val) + inner ℝ c.val ((t / 2) • c.val) = t
  simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm,
    one_pow, mul_one]
  ring

theorem surjective_fderiv_circleNorm (c : Sphere 1) :
    Surjective (fderiv ℝ circleNorm c.val) :=
  fun t ↦ ⟨circleNormal c t, circleNorm_rightInverse c t⟩

theorem orthogonalRightInverse_circleNorm (c : Sphere 1) :
    orthogonalRightInverse (fderiv ℝ circleNorm c.val) = circleNormal c := by
  apply orthogonalRightInverse_eq_of_rightInverse _ (surjective_fderiv_circleNorm c)
  · exact circleNorm_rightInverse c
  · rintro _ ⟨t, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro u hu
    have hD : fderiv ℝ circleNorm c.val u = 0 := hu
    rw [fderiv_circleNorm, two_smul] at hD
    change inner ℝ c.val u + inner ℝ c.val u = 0 at hD
    have hcu : inner ℝ c.val u = 0 := by linarith
    change inner ℝ (circleNormal c t) u = 0
    rw [circleNormal_apply, real_inner_smul_left, hcu, mul_zero]

end NoExoticSixSphere.CircleCylinder
