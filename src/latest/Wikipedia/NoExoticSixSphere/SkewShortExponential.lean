import Wikipedia.NoExoticSixSphere.SkewRotationExponential

/-!
# Endpoint angles for short skew exponentials

When the operator norm of `K` is at most `π`, each actual Gram eigenvector
has endpoint angle whose square is its Gram eigenvalue. Both the zero-speed
case and the positive rotation-plane case are included.
-/

namespace NoExoticSixSphere.SkewShortExponential

open GLOrthonormalization CayleyTransform SkewSpectralPlane SkewVectorODE
  SkewRotationExponential OrthogonalExponential

variable {n : ℕ}

theorem eigenvector_endpoint_angle_sq (K : SkewOperators n)
    (hK : ‖(K : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi) {x : Vector n} {μ : ℝ}
    (hx : ‖x‖ = 1) (he : gram K x = μ • x) :
    Real.arccos (inner ℝ x ((exp K).1.1 x)) ^ 2 = μ := by
  have hnorm : ‖(K : Vector n →L[ℝ] Vector n) x‖ ^ 2 = μ := by
    simpa only [hx, one_pow, mul_one] using norm_apply_sq_of_eigenvector K he
  by_cases hz : (K : Vector n →L[ℝ] Vector n) x = 0
  · have hex : (exp K).1.1 x = x := by
      simpa only [one_smul] using exp_apply_of_zero K hz 1
    rw [hz, norm_zero, zero_pow (by decide)] at hnorm
    rw [hex, real_inner_self_eq_norm_sq, hx, one_pow, Real.arccos_one]
    simpa using hnorm
  · have hμ : 0 < μ := by rw [← hnorm]; exact sq_pos_of_pos (norm_pos_iff.mpr hz)
    obtain ⟨α, y, hα, _, hxy, hKx, hKy, hsq⟩ := exists_rotationPartner K hμ hx he
    have hαnorm : α = ‖(K : Vector n →L[ℝ] Vector n) x‖ := by
      nlinarith [norm_nonneg ((K : Vector n →L[ℝ] Vector n) x)]
    have hαpi : α ≤ Real.pi := by
      rw [hαnorm]
      calc
        _ ≤ ‖(K : Vector n →L[ℝ] Vector n)‖ * ‖x‖ :=
          (K : Vector n →L[ℝ] Vector n).le_opNorm x
        _ ≤ Real.pi := by simpa only [hx, mul_one] using hK
    have hex := exp_apply_rotation K hKx hKy 1
    rw [one_smul, mul_one] at hex
    rw [hex, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hx, one_pow, hxy, mul_one, mul_zero, add_zero,
      Real.arccos_cos hα.le hαpi]
    exact hsq

end NoExoticSixSphere.SkewShortExponential
