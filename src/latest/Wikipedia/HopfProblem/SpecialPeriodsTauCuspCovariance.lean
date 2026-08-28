import Wikipedia.HopfProblem.SpecialPeriodsTauCuspContinuation

/-!
# Global parabolic covariance from the proved cusp expansion

The exact cusp formula gives clockwise covariance on a nonempty open
source cusp region. Both sides are analytic on the entire upper half-plane,
so the identity theorem makes this covariance global. The conclusion is
the literal translation by minus an integer, with no conjugation choice.
-/

open Filter Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

private theorem exists_native_source_cusp_point (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) :
    ∃ a : ℍ, ‖Function.Periodic.qParam w (a : ℂ)‖ < r := by
  obtain ⟨s, hs⟩ := logBase_set_nonempty (min r 1) (lt_min hr zero_lt_one)
  have hsn : ‖exponential s‖ < min r 1 := (CuspFamily.mem_logBase (min r 1) s).mp hs
  have hspos : 0 < s.im := upperHalfPlane_of_exponential_norm_lt_one
    (lt_of_lt_of_le hsn (min_le_right r 1))
  have hswpos : 0 < (s * (w : ℂ)).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add] using mul_pos hspos hw
  refine ⟨⟨s * w, hswpos⟩, ?_⟩
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  simpa only [qParam_eq_exponential_div, mul_div_cancel_right₀ _ hwC] using
    lt_of_lt_of_le hsn (min_le_left r 1)

private theorem sub_int_mul_width_im_pos (w : ℝ) (k : ℤ) {s : ℂ} (hs : 0 < s.im) :
    0 < (s - (k : ℂ) * w).im := by
  simpa only [Complex.sub_im, Complex.mul_im, Complex.intCast_im,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero] using hs

/-- Global clockwise covariance follows from global native holomorphy and
the actual cusp formula. No covariance or target cusp bound is assumed;
even analyticity of the correction is unnecessary for this consequence. -/
theorem global_native_sub_int_mul_width_of_cuspFormula (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    (hcusp : ∀ z : ℍ, ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
      (τ z : ℂ) = correctedLogarithmWidth w h z)
    (k : ℤ) (z : ℍ) :
    (τ (ofComplex ((z : ℂ) - (k : ℂ) * w)) : ℂ) = (τ z : ℂ) - k := by
  have hleft : AnalyticOnNhd ℂ
      (fun s : ℂ => (τ (ofComplex (s - (k : ℂ) * w)) : ℂ)) upperHalfPlaneSet := by
    intro s hs
    have hshift : AnalyticAt ℂ (fun t : ℂ => t - (k : ℂ) * w) s :=
      analyticAt_id.sub analyticAt_const
    exact (upperHalfPlane_ambient_analyticAt hτ (sub_int_mul_width_im_pos w k hs)).comp
      (f := fun t : ℂ => t - (k : ℂ) * w) (x := s) hshift
  have hright : AnalyticOnNhd ℂ
      (fun s : ℂ => (τ (ofComplex s) : ℂ) - k) upperHalfPlaneSet :=
    fun s hs => (upperHalfPlane_ambient_analyticAt hτ hs).sub analyticAt_const
  have hconnected : IsPreconnected upperHalfPlaneSet :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm).isPreconnected
  obtain ⟨a, ha⟩ := exists_native_source_cusp_point w hw hr
  have hcuspAmbient {s : ℂ} (hs : 0 < s.im)
      (hsq : ‖Function.Periodic.qParam w s‖ < r) :
      (τ (ofComplex s) : ℂ) = correctedLogarithmWidth w h s := by
    simpa only [ofComplex_apply_of_im_pos hs] using hcusp ⟨s, hs⟩ hsq
  have hqOpen : IsOpen {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
    isOpen_lt (Function.Periodic.continuous_qParam (h := w)).norm continuous_const
  have heq : (fun s : ℂ => (τ (ofComplex (s - (k : ℂ) * w)) : ℂ)) =ᶠ[𝓝 (a : ℂ)]
      (fun s : ℂ => (τ (ofComplex s) : ℂ) - k) := by
    filter_upwards [hqOpen.mem_nhds ha, isOpen_upperHalfPlaneSet.mem_nhds a.im_pos]
      with s hsq hs
    have hskq : ‖Function.Periodic.qParam w (s - (k : ℂ) * w)‖ < r := by
      rw [qParam_sub_int_mul_width w hw.ne']
      exact hsq
    rw [hcuspAmbient (sub_int_mul_width_im_pos w k hs) hskq,
      hcuspAmbient hs hsq, correctedLogarithmWidth_sub_int_mul_width w hw.ne']
  have hglobal := hleft.eqOn_of_preconnected_of_eventuallyEq hright hconnected a.im_pos heq
  have hz : (τ (ofComplex ((z : ℂ) - (k : ℂ) * w)) : ℂ) =
      (τ (ofComplex (z : ℂ)) : ℂ) - k := hglobal z.im_pos
  simpa only [ofComplex_apply] using hz

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
