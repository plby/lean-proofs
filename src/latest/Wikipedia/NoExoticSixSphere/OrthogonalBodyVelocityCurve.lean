import Wikipedia.NoExoticSixSphere.OrthogonalExponentialVariation
import Wikipedia.NoExoticSixSphere.OrthogonalConstantVelocity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The smooth skew-adjoint body-velocity curve

The actual body velocity of a smooth orthogonal curve is a smooth map to the
skew-adjoint model. Its derivative agrees with the time derivative appearing
in the first variation, independently of the chosen exponential variation.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalBodyVelocityCurve

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalVelocity
  OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ} {γ : ℝ → OrthogonalOperators n}
  (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1))

noncomputable def body (t : ℝ) : SkewOperators n :=
  bodyVelocity γ (deriv (fun r ↦ (γ r).1.1) t) t
    (((hγ.differentiable (by simp)) t).hasDerivAt)

theorem body_coe (t : ℝ) :
    (body hγ t : Vector n →L[ℝ] Vector n) =
      (inverse (γ t)).1.1.comp (deriv (fun r ↦ (γ r).1.1) t) := rfl

theorem contDiff_body : ContDiff ℝ ∞ (body hγ) := by
  let L : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hi : ContDiff ℝ ∞ (fun t ↦ (inverse (γ t)).1.1) := by
    simpa only [L, inverse_eq_adjoint] using! L.contDiff.comp hγ
  have hb : ContDiff ℝ ∞ (fun t ↦ (body hγ t : Vector n →L[ℝ] Vector n)) :=
    hi.clm_comp hγ.deriv'
  have hp := (CayleyAtlas.skewProjection (n := n)).contDiff.comp hb
  simpa only [Function.comp_def, CayleyAtlas.skewProjection_coe] using hp

theorem hasDerivAt_body_coe (t : ℝ) :
    HasDerivAt (fun r ↦ (body hγ r : Vector n →L[ℝ] Vector n))
      ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n) t := by
  let L : SkewOperators n →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL
  exact L.hasFDerivAt.comp_hasDerivAt t
    ((((contDiff_body hγ).differentiable (by simp)) t).hasDerivAt)

variable {W : ℝ → SkewOperators n} (hW : ContDiff ℝ ∞ W)

include hW

theorem velocity_family_zero (t : ℝ) :
    velocity (OrthogonalExponentialVariation.family γ W) (0, t) =
      (body hγ t : Vector n →L[ℝ] Vector n) := by
  have hA := OrthogonalExponentialVariation.contDiff_family_operator hγ hW
  have hd := hasDerivAt_second ((hA.differentiable (by simp)) (0, t))
  have heq : (fun r ↦ (OrthogonalExponentialVariation.family γ W (0, r)).1.1) =
      (fun r ↦ (γ r).1.1) := by
    funext r
    rw [OrthogonalExponentialVariation.family_zero]
  change HasDerivAt (fun r ↦ (OrthogonalExponentialVariation.family γ W (0, r)).1.1)
    (second (operator (OrthogonalExponentialVariation.family γ W)) (0, t)) t at hd
  rw [heq] at hd
  have he := hd.unique (((hγ.differentiable (by simp)) t).hasDerivAt)
  unfold velocity
  rw [he, OrthogonalExponentialVariation.family_zero]
  rfl

theorem second_velocity_family_zero (t : ℝ) :
    second (velocity (OrthogonalExponentialVariation.family γ W)) (0, t) =
      ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n) := by
  have hv := contDiff_velocity (OrthogonalExponentialVariation.contDiff_family_operator hγ hW)
  have hd := hasDerivAt_second ((hv.differentiable (by simp)) (0, t))
  have heq : (fun r ↦ velocity (OrthogonalExponentialVariation.family γ W) (0, r)) =
      (fun r ↦ (body hγ r : Vector n →L[ℝ] Vector n)) :=
    funext (velocity_family_zero hγ hW)
  rw [heq] at hd
  exact hd.unique (hasDerivAt_body_coe hγ t)

end NoExoticSixSphere.OrthogonalBodyVelocityCurve
