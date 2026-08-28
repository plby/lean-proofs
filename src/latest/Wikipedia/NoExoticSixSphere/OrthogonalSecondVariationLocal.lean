import Wikipedia.NoExoticSixSphere.OrthogonalEnergyDerivative

/-!
# Local second variation at a constant-body-velocity path

The mixed derivative of body velocity is computed from the Maurer--Cartan
identity. This identifies the actual second-energy-derivative integrand at an
exponential path, before integration by parts.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalFirstVariation

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalCommutator
  OrthogonalMaurerCartan TwoParameterCalculus

variable {n : ℕ} {a : ℝ × ℝ → OrthogonalOperators n}
  (ha : ContDiff ℝ ∞ (operator a))

include ha

theorem second_first_velocity_of_constant (s : ℝ) (K : SkewOperators n)
    (hK : ∀ t, velocity a (s, t) = (K : Vector n →L[ℝ] Vector n)) (t : ℝ) :
    second (first (velocity a)) (s, t) = second (second (variation a)) (s, t) +
      commutator (K : Vector n →L[ℝ] Vector n) (second (variation a) (s, t)) := by
  have heq : (fun r ↦ first (velocity a) (s, r)) =
      (fun r ↦ second (variation a) (s, r) +
        commutator (K : Vector n →L[ℝ] Vector n) (variation a (s, r))) := by
    funext r
    rw [maurer_cartan ha, hK]
  have hd := hasDerivAt_second
    (((contDiff_first (contDiff_velocity ha)).differentiable (by simp)) (s, t))
  rw [heq] at hd
  have hright := (hasDerivAt_second
    (((contDiff_second (contDiff_variation ha)).differentiable (by simp)) (s, t))).add
      (hasDerivAt_commutator (hasDerivAt_const t (K : Vector n →L[ℝ] Vector n))
        (hasDerivAt_second (((contDiff_variation ha).differentiable (by simp)) (s, t))))
  have hz (B : Vector n →L[ℝ] Vector n) : commutator 0 B = 0 := by
    simp [OrthogonalCommutator.commutator]
  simpa only [hz, zero_add] using hd.unique hright

theorem first_accelerationPairing_of_constant (s : ℝ) (K : SkewOperators n)
    (hK : ∀ t, velocity a (s, t) = (K : Vector n →L[ℝ] Vector n)) (t : ℝ) :
    first (accelerationPairing a) (s, t) =
      innerForm (second (second (variation a)) (s, t) +
        commutator (K : Vector n →L[ℝ] Vector n) (second (variation a) (s, t)))
        (variation a (s, t)) := by
  rw [first_accelerationPairing ha,
    second_velocity_eq_zero_of_constant ha s (K : Vector n →L[ℝ] Vector n) hK,
    first_second (contDiff_velocity ha), second_first_velocity_of_constant ha s K hK]
  have hz (B : Vector n →L[ℝ] Vector n) : innerForm 0 B = 0 := by simp [innerForm]
  rw [hz, zero_add]

end NoExoticSixSphere.OrthogonalFirstVariation
