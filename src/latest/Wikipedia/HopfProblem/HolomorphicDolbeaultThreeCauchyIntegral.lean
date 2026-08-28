import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchyBasic

/-!
# Cauchy–Green commutes with antiholomorphic parameter differentiation

The parameter identity is obtained by applying a continuous real-linear
functional to the already proved operator-valued derivative integral.  The
last-coordinate solution and recovery identities are the actual one-variable
Cauchy–Green identities on each slice.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff Convolution

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cauchy

open HolomorphicCousin PeriodTorusLineBundleClassification

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- In the integrated coordinate, Cauchy–Green solves the actual
antiholomorphic derivative equation with an arbitrary real parameter. -/
theorem lastDbar_cauchySecond {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    lastDbar (cauchySecond f) q = f q := by
  exact dbar_cauchyGreen (hf.comp (contDiff_prodMk_right q.1))
    (hasCompactSupport_slice hk hfk q.1) q.2

/-- Cauchy–Green recovers the function from its last-coordinate derivative
when the function has the stated uniform compact support. -/
theorem cauchySecond_lastDbar {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    cauchySecond (lastDbar f) q = f q := by
  exact cauchyGreen_dbar (hf.comp (contDiff_prodMk_right q.1))
    (hasCompactSupport_slice hk hfk q.1) q.2

/-- The recovery integral is convergent, not a use of the totalized integral
on nonintegrable data. -/
theorem integrable_cauchySecond_lastDbar {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * lastDbar f (q.1, q.2 - w)) :=
  integrable_cauchySecond (continuous_lastDbar hf) hk
    (fun p _ hw => lastDbar_eq_zero_off_second_support hk.isClosed hfk p hw) q

section ComplexParameter

variable [NormedSpace ℂ P]

/-- Antiholomorphic differentiation in any fixed parameter direction passes
through the convergent Cauchy–Green integral in the last coordinate. -/
theorem parameterDbar_cauchySecond (v : P) {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    parameterDbar v (cauchySecond f) q = cauchySecond (parameterDbar v f) q := by
  have hi : Integrable (fun w : ℂ =>
      (ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ) w⁻¹
        (fderiv ℝ f (q.1, q.2 - w))) :=
    (hasCompactSupport_fderiv_slice hk hfk q.1).convolutionExists_right
      ((ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ))
      locallyIntegrable_complex_inv
      ((hf.continuous_fderiv one_ne_zero).comp
        (continuous_const.prodMk continuous_id)) q.2
  change parameterLinear v (fderiv ℝ (cauchySecond f) q) = _
  rw [(hasFDerivAt_cauchySecond hf hk hfk q).fderiv,
    parameterLinear_complex_smul, convolution_def,
    ← (parameterLinear v).integral_comp_comm hi]
  unfold cauchySecond cauchyGreen
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  exact parameterLinear_complex_smul v _ _

/-- The differentiated Cauchy–Green integral is convergent. -/
theorem integrable_cauchySecond_parameterDbar (v : P)
    {f : P × ℂ → ℂ} {k : Set ℂ} (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * parameterDbar v f (q.1, q.2 - w)) :=
  integrable_cauchySecond (continuous_parameterDbar v hf) hk
    (fun p _ hw => parameterDbar_eq_zero_off_second_support v hk.isClosed hfk p hw) q

/-- Vanishing of a parameter antiholomorphic derivative along a whole slice
is preserved by the integral in the last coordinate. -/
theorem parameterDbar_cauchySecond_eq_zero (v : P)
    {f : P × ℂ → ℂ} {k : Set ℂ} (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (p : P)
    (hd : ∀ w, parameterDbar v f (p, w) = 0) (z : ℂ) :
    parameterDbar v (cauchySecond f) (p, z) = 0 := by
  rw [parameterDbar_cauchySecond v hf hk hfk]
  simp only [cauchySecond, cauchyGreen, hd, mul_zero, integral_zero]

end ComplexParameter

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cauchy
