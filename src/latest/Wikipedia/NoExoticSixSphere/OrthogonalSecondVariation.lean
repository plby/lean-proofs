import Wikipedia.NoExoticSixSphere.OrthogonalSecondVariationLocal
import Wikipedia.NoExoticSixSphere.OrthogonalIndexForm

/-!
# Second variation of energy at an orthogonal exponential path

For every smooth fixed-endpoint variation through an exponential base path,
the actual second derivative of integral energy equals the quadratic index
form. The field in that form is the variation's actual left-trivialized
parameter derivative; it is not independent input data.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalFirstVariation

open GLOrthonormalization CayleyTransform OrthogonalPathEnergy OrthogonalExponential
  OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ} {a : ℝ × ℝ → OrthogonalOperators n}
  (ha : ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator a))

include ha

theorem hasDerivAt_deriv_energy_of_constantVelocity (l u : ℝ)
    (hl : ∀ r, a (r, l) = a (0, l)) (hu : ∀ r, a (r, u) = a (0, u))
    (s : ℝ) (K : SkewOperators n)
    (hK : ∀ t, velocity a (s, t) = (K : Vector n →L[ℝ] Vector n)) :
    HasDerivAt (deriv (fun r ↦ energy
      (fun t ↦ OrthogonalMaurerCartan.operator a (r, t)) l u))
      (2 * ∫ t in l..u, OrthogonalIndexForm.density K
        (variation a (s, t)) (second (variation a) (s, t))) s := by
  apply (hasDerivAt_deriv_energy ha l u hl hu s).congr_deriv
  calc
    _ = -2 * ∫ t in l..u, HilbertSchmidt.innerForm
        (second (second (variation a)) (s, t) +
          OrthogonalCommutator.commutator (K : Vector n →L[ℝ] Vector n)
            (second (variation a) (s, t))) (variation a (s, t)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      exact first_accelerationPairing_of_constant ha s K hK t
    _ = _ := OrthogonalIndexForm.integral_secondDerivative K
      ((contDiff_variation ha).continuous.comp
        (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t))))
      ((contDiff_second (contDiff_variation ha)).continuous.comp
        (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t))))
      ((contDiff_second (contDiff_second (contDiff_variation ha))).continuous.comp
        (continuous_const.prodMk continuous_id : Continuous (fun t : ℝ ↦ (s, t))))
      (fun t ↦ hasDerivAt_second
        (((contDiff_variation ha).differentiable (by simp)) (s, t)))
      (fun t ↦ hasDerivAt_second
        (((contDiff_second (contDiff_variation ha)).differentiable (by simp)) (s, t)))
      l u
      (variation_eq_zero_of_constant_slice ha l s (fun r ↦ (hl r).trans (hl s).symm))
      (variation_eq_zero_of_constant_slice ha u s (fun r ↦ (hu r).trans (hu s).symm))

/-- The index form is the actual second energy derivative at an exponential base path. -/
theorem hasDerivAt_deriv_energy_of_exponential (l u : ℝ)
    (hl : ∀ r, a (r, l) = a (0, l)) (hu : ∀ r, a (r, u) = a (0, u))
    (s : ℝ) (b : OrthogonalOperators n) (K : SkewOperators n)
    (hpath : ∀ t, a (s, t) = b * exp (t • K)) :
    HasDerivAt (deriv (fun r ↦ energy
      (fun t ↦ OrthogonalMaurerCartan.operator a (r, t)) l u))
      (2 * ∫ t in l..u, OrthogonalIndexForm.density K
        (variation a (s, t)) (second (variation a) (s, t))) s :=
  hasDerivAt_deriv_energy_of_constantVelocity ha l u hl hu s K
    (velocity_of_exponential_slice ha s b K hpath)

end NoExoticSixSphere.OrthogonalFirstVariation
