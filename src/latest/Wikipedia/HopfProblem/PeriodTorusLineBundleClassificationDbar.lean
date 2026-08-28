import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCauchy

/-!
# The two antiholomorphic coordinate derivatives

The coordinate derivatives are the ordinary one-variable `∂̄` derivatives
of slices.  Their descriptions in terms of the joint real derivative show
that Cauchy–Green in the second coordinate commutes with `∂̄` in the first.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ContDiff Convolution

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open HolomorphicCousin

def dbarFirst (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  dbar (fun z => f (z, q.2)) q.1

def dbarSecond (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  dbar (fun w => f (q.1, w)) q.2

def dbarFirstLinear : ((ℂ × ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.apply ℝ ℂ (1, 0) +
    I • ContinuousLinearMap.apply ℝ ℂ (I, 0))

def dbarSecondLinear : ((ℂ × ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) • (ContinuousLinearMap.apply ℝ ℂ (0, 1) +
    I • ContinuousLinearMap.apply ℝ ℂ (0, I))

@[simp] theorem dbarFirstLinear_apply (L : (ℂ × ℂ) →L[ℝ] ℂ) :
    dbarFirstLinear L = (L (1, 0) + I * L (I, 0)) / 2 := by
  simp only [dbarFirstLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

@[simp] theorem dbarSecondLinear_apply (L : (ℂ × ℂ) →L[ℝ] ℂ) :
    dbarSecondLinear L = (L (0, 1) + I * L (0, I)) / 2 := by
  simp only [dbarSecondLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem dbarFirst_eq_linear {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) :
    dbarFirst f q = dbarFirstLinear (fderiv ℝ f q) := by
  have he := (hf.hasFDerivAt.comp q.1
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2)).fderiv
  change fderiv ℝ (fun z => f (z, q.2)) q.1 = _ at he
  simp only [dbarFirst, dbar, he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, dbarFirstLinear_apply]

theorem dbarSecond_eq_linear {f : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (hf : DifferentiableAt ℝ f q) :
    dbarSecond f q = dbarSecondLinear (fderiv ℝ f q) := by
  have he := (hf.hasFDerivAt.comp q.2
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv
  change fderiv ℝ (fun w => f (q.1, w)) q.2 = _ at he
  simp only [dbarSecond, dbar, he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, dbarSecondLinear_apply]

theorem dbarFirstLinear_complex_smul (c : ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) :
    dbarFirstLinear (c • L) = c * dbarFirstLinear L := by
  simp only [dbarFirstLinear_apply, smul_apply, smul_eq_mul]
  ring

theorem dbarSecondLinear_complex_smul (c : ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) :
    dbarSecondLinear (c • L) = c * dbarSecondLinear L := by
  simp only [dbarSecondLinear_apply, smul_apply, smul_eq_mul]
  ring

theorem contDiff_dbarFirst {f : ℂ × ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dbarFirst f) := by
  have he : dbarFirst f = dbarFirstLinear ∘ fderiv ℝ f :=
    funext (fun q => dbarFirst_eq_linear ((hf.differentiable (by simp)) q))
  rw [he]
  exact dbarFirstLinear.contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

theorem contDiff_dbarSecond {f : ℂ × ℂ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dbarSecond f) := by
  have he : dbarSecond f = dbarSecondLinear ∘ fderiv ℝ f :=
    funext (fun q => dbarSecond_eq_linear ((hf.differentiable (by simp)) q))
  rw [he]
  exact dbarSecondLinear.contDiff.comp (contDiff_infty_iff_fderiv.mp hf).2

/-- The parameter antiholomorphic derivative commutes with the convergent
integral in the other coordinate. -/
theorem dbarFirst_cauchySecond {f : ℂ × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, w ∉ k → f (z, w) = 0) (q : ℂ × ℂ) :
    dbarFirst (cauchySecond f) q = cauchySecond (dbarFirst f) q := by
  have hi : Integrable (fun w : ℂ =>
      (ContinuousLinearMap.mul ℝ ℂ).precompR (ℂ × ℂ) w⁻¹
        (fderiv ℝ f (q.1, q.2 - w))) :=
    (hasCompactSupport_fderiv_slice hk hfk q.1).convolutionExists_right
      ((ContinuousLinearMap.mul ℝ ℂ).precompR (ℂ × ℂ))
      locallyIntegrable_complex_inv
      ((hf.continuous_fderiv one_ne_zero).comp
        (continuous_const.prodMk continuous_id)) q.2
  rw [dbarFirst_eq_linear (hasFDerivAt_cauchySecond hf hk hfk q).differentiableAt,
    (hasFDerivAt_cauchySecond hf hk hfk q).fderiv,
    dbarFirstLinear_complex_smul, convolution_def,
    ← dbarFirstLinear.integral_comp_comm hi]
  unfold cauchySecond cauchyGreen
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  rw [dbarFirst_eq_linear ((hf.differentiable one_ne_zero) _)]
  exact dbarFirstLinear_complex_smul _ _

/-- In the integrated coordinate the same integral solves the actual
antiholomorphic derivative equation. -/
theorem dbarSecond_cauchySecond {f : ℂ × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, w ∉ k → f (z, w) = 0) (q : ℂ × ℂ) :
    dbarSecond (cauchySecond f) q = f q := by
  exact dbar_cauchyGreen (hf.comp (contDiff_prodMk_right q.1))
    (hasCompactSupport_slice hk hfk q.1) q.2

/-- The integral recovers a supported function from its second-coordinate
antiholomorphic derivative. -/
theorem cauchySecond_dbarSecond {f : ℂ × ℂ → ℂ} {k : Set ℂ}
    (hf : ContDiff ℝ 1 f) (hk : IsCompact k)
    (hfk : ∀ z w, w ∉ k → f (z, w) = 0) (q : ℂ × ℂ) :
    cauchySecond (dbarSecond f) q = f q := by
  exact cauchyGreen_dbar (hf.comp (contDiff_prodMk_right q.1))
    (hasCompactSupport_slice hk hfk q.1) q.2

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
