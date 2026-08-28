import Wikipedia.HopfProblem.HolomorphicCousinConvolutionSolution

/-!
# Cauchy–Green with a genuine extra parameter

The one-variable integral is smooth jointly with its parameter, provided the
support in the integrated variable lies in one compact set.  Its total real
derivative is the integral of the total derivative of the data.  These are
analytic prerequisites for descent on the universal cover, not an assumed
Cousin theorem or an assumed trivialization of a pulled-back line bundle.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped ContDiff Convolution Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Cauchy–Green in the second coordinate, leaving the first as a parameter. -/
def cauchySecond (f : P × ℂ → ℂ) (q : P × ℂ) : ℂ :=
  cauchyGreen (fun w => f (q.1, w)) q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Uniform compact support in the integrated coordinate gives compactly
supported slices.  The parameter itself need not have compact support. -/
theorem hasCompactSupport_slice {f : P × ℂ → ℂ} {k : Set ℂ}
    (hk : IsCompact k) (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (p : P) :
    HasCompactSupport (fun w => f (p, w)) :=
  HasCompactSupport.intro hk (hfk p)

omit [NormedSpace ℝ P] in
/-- The defining integral converges for every parameter and evaluation point. -/
theorem integrable_cauchySecond {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : Continuous f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * f (q.1, q.2 - w)) :=
  integrable_cauchyGreen (hf.comp (continuous_const.prodMk continuous_id))
    (hasCompactSupport_slice hk hfk q.1) q.2

/-- Joint smoothness follows from the actual parametric convolution theorem. -/
theorem contDiff_cauchySecond {n : ℕ∞} {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ n f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) :
    ContDiff ℝ n (cauchySecond f) := by
  have h := contDiffOn_convolution_right_with_param
    (ContinuousLinearMap.mul ℝ ℂ) (g := fun p w => f (p, w))
    isOpen_univ hk (fun p w _ hw => hfk p w hw)
    locallyIntegrable_complex_inv hf.contDiffOn
  have hconv : ContDiff ℝ n (fun q : P × ℂ =>
      ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ]
        (fun w => f (q.1, w))) q.2) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using h
  exact contDiff_const.mul hconv

/-- Every total derivative vanishes outside the common support in the second
coordinate.  This includes derivatives in the parameter direction. -/
theorem fderiv_eq_zero_off_second_support {f : P × ℂ → ℂ} {k : Set ℂ}
    (hk : IsClosed k) (hfk : ∀ p w, w ∉ k → f (p, w) = 0)
    (p : P) {w : ℂ} (hw : w ∉ k) : fderiv ℝ f (p, w) = 0 := by
  apply (hasFDerivAt_zero_of_eventually_const (0 : ℂ) ?_).fderiv
  have hn : Prod.snd ⁻¹' kᶜ ∈ 𝓝 (p, w) :=
    (hk.isOpen_compl.preimage continuous_snd).mem_nhds hw
  filter_upwards [hn] with q hq
  exact hfk q.1 q.2 hq

theorem hasCompactSupport_fderiv_slice {f : P × ℂ → ℂ} {k : Set ℂ}
    (hk : IsCompact k) (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (p : P) :
    HasCompactSupport (fun w => fderiv ℝ f (p, w)) :=
  HasCompactSupport.intro hk (fun _ hw =>
    fderiv_eq_zero_off_second_support hk.isClosed hfk p hw)

/-- The total derivative is a convergent operator-valued convolution. -/
theorem hasFDerivAt_cauchySecond {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q : P × ℂ) :
    HasFDerivAt (cauchySecond f)
      ((1 / (Real.pi : ℂ)) •
        ((fun w : ℂ => w⁻¹) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ)]
          (fun w => fderiv ℝ f (q.1, w))) q.2) q := by
  convert! (hasFDerivAt_convolution_right_with_param
    (ContinuousLinearMap.mul ℝ ℂ) (g := fun p w => f (p, w))
    isOpen_univ hk (fun p w _ hw => hfk p w hw)
    locallyIntegrable_complex_inv hf.contDiffOn q (mem_univ _)).const_mul
      (1 / (Real.pi : ℂ)) using 1

/-- Differentiation in any joint parameter/coordinate direction passes through
the actual Cauchy–Green integral. -/
theorem fderiv_cauchySecond_apply {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q v : P × ℂ) :
    fderiv ℝ (cauchySecond f) q v =
      (1 / (Real.pi : ℂ)) *
        ∫ w : ℂ, w⁻¹ * fderiv ℝ f (q.1, q.2 - w) v := by
  rw [(hasFDerivAt_cauchySecond hf hk hfk q).fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    locallyIntegrable_complex_inv (hasCompactSupport_fderiv_slice hk hfk q.1)
    ((hf.continuous_fderiv one_ne_zero).comp
      (continuous_const.prodMk continuous_id))]
  rfl

/-- Each differentiated scalar integrand is integrable. -/
theorem integrable_cauchySecond_fderiv {f : P × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ p w, w ∉ k → f (p, w) = 0) (q v : P × ℂ) :
    Integrable (fun w : ℂ => w⁻¹ * fderiv ℝ f (q.1, q.2 - w) v) := by
  refine integrable_cauchyGreen (f := fun w => fderiv ℝ f (q.1, w) v) ?_ ?_ q.2
  · exact (((hf.continuous_fderiv one_ne_zero).comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const)
  · exact HasCompactSupport.intro hk (fun w hw => by
      rw [fderiv_eq_zero_off_second_support hk.isClosed hfk q.1 hw]
      rfl)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
