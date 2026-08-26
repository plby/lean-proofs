import ErdosProblems.Erdos1002.FixedAwayFourierDecay
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Vanishing of the fixed-away principal-value multiplier at infinity

The transform `Rχ` is not the ordinary Fourier transform of an `L¹`
function, because `χ(v) / v` has a nonintegrable absolute tail.  On the
positive half-line we split it at the fixed cutoff radius.  The compact part
is the Fourier transform of an honest `L¹` quotient (the cutoff vanishes on a
neighbourhood of zero), while the remaining `1/v` tail is controlled by the
already proved Dirichlet sine-tail estimate.  This gives the cancellation at
infinity without subtracting two conditionally convergent integrals.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

/-- The compact positive-half-line quotient used in the
Riemann--Lebesgue step. -/
def fixedAwayPositiveQuotient (t δ x : ℝ) : ℂ :=
  (Ioc (0 : ℝ) t).indicator
    (fun v : ℝ ↦ ((fixedAwaySmoothCutoff t δ v / v : ℝ) : ℂ)) x

theorem measurable_fixedAwayPositiveQuotient (t δ : ℝ) :
    Measurable (fixedAwayPositiveQuotient t δ) := by
  unfold fixedAwayPositiveQuotient
  apply Measurable.indicator _ measurableSet_Ioc
  exact Complex.ofRealCLM.measurable.comp
    ((fixedAwaySmoothCutoff_contDiff (m := (⊤ : ℕ∞)) t δ).continuous.measurable.div
      measurable_id)

theorem integrable_fixedAwayPositiveQuotient
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    Integrable (fixedAwayPositiveQuotient t δ) volume := by
  let q : ℝ → ℂ :=
    fun v ↦ ((fixedAwaySmoothCutoff t δ v / v : ℝ) : ℂ)
  have hgap : 0 < t - δ := sub_pos.mpr hδt
  have hqmeas : AEStronglyMeasurable q (volume.restrict (Ioc (0 : ℝ) t)) := by
    exact (Complex.ofRealCLM.measurable.comp
      ((fixedAwaySmoothCutoff_contDiff (m := (⊤ : ℕ∞)) t δ).continuous.measurable.div
        measurable_id)).aestronglyMeasurable
  have hqbound : ∀ᵐ v ∂volume.restrict (Ioc (0 : ℝ) t),
      ‖q v‖ ≤ (t - δ)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hvpos : 0 < v := hv.1
    by_cases hlarge : t - δ ≤ v
    · have hcut := fixedAwaySmoothCutoff_mem_Icc hδ hδt.le v
      dsimp [q]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
        abs_of_nonneg hcut.1, abs_of_pos hvpos]
      simpa only [one_div] using!
        (div_le_div₀ zero_le_one hcut.2 hgap hlarge)
    · have hvsmall : |v| ≤ t - δ := by
        rw [abs_of_pos hvpos]
        exact (lt_of_not_ge hlarge).le
      rw [show q v = 0 by
        dsimp [q]
        rw [fixedAwaySmoothCutoff_eq_zero_of_abs_le_sub hδ hvsmall,
          zero_div, Complex.ofReal_zero]]
      simpa using! inv_nonneg.mpr hgap.le
  have hqint : IntegrableOn q (Ioc (0 : ℝ) t) volume :=
    IntegrableOn.of_bound measure_Ioc_lt_top hqmeas (t - δ)⁻¹ hqbound
  simpa only [fixedAwayPositiveQuotient, q] using!
    hqint.integrable_indicator measurableSet_Ioc

/-- The compact sine transform is the negative imaginary part of the
ordinary Fourier transform of the compact quotient. -/
theorem integral_fixedAwayCutoff_sine_eq_neg_im_fourier
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (y : ℝ) :
    (∫ v in (0 : ℝ)..t,
        fixedAwaySmoothCutoff t δ v *
          sineKernel (2 * Real.pi * y) v) =
      -(FourierTransform.fourier
          (fixedAwayPositiveQuotient t δ) y).im := by
  let f : ℝ → ℂ := fixedAwayPositiveQuotient t δ
  let g : ℝ → ℂ := fun v ↦
    Complex.exp (((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I) * f v
  have hfint : Integrable f volume :=
    integrable_fixedAwayPositiveQuotient hδ hδt
  have hgint : Integrable g volume := by
    apply hfint.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with v
      rw [Complex.norm_exp]
      simp
  have him := Complex.imCLM.integral_comp_comm hgint
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ v in (0 : ℝ)..t,
      fixedAwaySmoothCutoff t δ v *
        sineKernel (2 * Real.pi * y) v) = -((∫ v : ℝ, g v).im)
  have him' : (∫ v : ℝ, g v).im = ∫ v : ℝ, (g v).im := by
    simpa only [Complex.imCLM_apply] using! him.symm
  rw [him']
  have hpoint (v : ℝ) :
      -(g v).im =
        (Ioc (0 : ℝ) t).indicator
          (fun x : ℝ ↦ fixedAwaySmoothCutoff t δ x *
            sineKernel (2 * Real.pi * y) x) v := by
    by_cases hv : v ∈ Ioc (0 : ℝ) t
    · have hv0 : v ≠ 0 := hv.1.ne'
      by_cases hy : y = 0
      · subst y
        simp [g, f, fixedAwayPositiveQuotient, hv, sineKernel]
      · have harg : (2 * Real.pi * y) * v ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by positivity) hy) hv0
        simp only [g, f, fixedAwayPositiveQuotient,
          indicator_of_mem hv, Complex.exp_ofReal_mul_I_im,
          Complex.exp_ofReal_mul_I_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero]
        rw [show -2 * Real.pi * v * y =
          -(2 * Real.pi * y * v) by ring, Real.sin_neg]
        rw [sineKernel, Real.sinc_of_ne_zero harg]
        field_simp
        ring
    · simp only [g, f, fixedAwayPositiveQuotient,
        indicator_of_notMem hv, mul_zero, Complex.zero_im, neg_zero]
  calc
    (∫ v in (0 : ℝ)..t,
        fixedAwaySmoothCutoff t δ v *
          sineKernel (2 * Real.pi * y) v) =
        ∫ v : ℝ,
          (Ioc (0 : ℝ) t).indicator
            (fun x : ℝ ↦ fixedAwaySmoothCutoff t δ x *
              sineKernel (2 * Real.pi * y) x) v := by
      rw [integral_indicator measurableSet_Ioc]
      exact intervalIntegral.integral_of_le (hδ.le.trans hδt.le)
    _ = ∫ v : ℝ, -(g v).im := by
      apply integral_congr_ae
      filter_upwards with v
      exact (hpoint v).symm
    _ = -(∫ v : ℝ, (g v).im) := by rw [integral_neg]

/-- The compact positive-half-line contribution tends to zero with the
frequency. -/
theorem tendsto_integral_fixedAwayCutoff_sine_atTop
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    Tendsto
      (fun y : ℝ ↦ ∫ v in (0 : ℝ)..t,
        fixedAwaySmoothCutoff t δ v *
          sineKernel (2 * Real.pi * y) v)
      atTop (nhds 0) := by
  have hfour : Tendsto
      (FourierTransform.fourier (fixedAwayPositiveQuotient t δ))
      atTop (nhds 0) :=
    (Real.zero_at_infty_fourier (fixedAwayPositiveQuotient t δ)).mono_left
      atTop_le_cocompact
  have him : Tendsto
      (fun y ↦ -(FourierTransform.fourier
        (fixedAwayPositiveQuotient t δ) y).im)
      atTop (nhds 0) := by
    simpa using! (Complex.continuous_im.tendsto 0).comp hfour |>.neg
  apply him.congr'
  filter_upwards with y
  exact (integral_fixedAwayCutoff_sine_eq_neg_im_fourier hδ hδt y).symm

/-- At a fixed positive truncation radius, the quantitative Dirichlet
sine-integral tail tends to zero as the frequency tends to `+∞`. -/
theorem tendsto_dirichletSineLimit_sub_sineIntegralTruncation_atTop
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun y : ℝ ↦ dirichletSineLimit (2 * Real.pi * y) -
        sineIntegralTruncation (2 * Real.pi * y) t)
      atTop (nhds 0) := by
  have hlin : Tendsto (fun y : ℝ ↦ 2 * Real.pi * y) atTop atTop :=
    tendsto_id.const_mul_atTop (mul_pos (by norm_num) Real.pi_pos)
  have hinv : Tendsto (fun y : ℝ ↦ (2 * Real.pi * y)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hlin
  have hupperRaw : Tendsto
      (fun y : ℝ ↦ 3 * ((2 * Real.pi * y)⁻¹ * t⁻¹))
      atTop (nhds 0) := by
    have hthree : Tendsto (fun _y : ℝ ↦ (3 : ℝ)) atTop (nhds 3) :=
      tendsto_const_nhds
    have htinv : Tendsto (fun _y : ℝ ↦ t⁻¹) atTop (nhds t⁻¹) :=
      tendsto_const_nhds
    simpa only [zero_mul, mul_zero] using! hthree.mul (hinv.mul htinv)
  have hupper : Tendsto
      (fun y : ℝ ↦ 3 * (|2 * Real.pi * y|⁻¹ * t⁻¹))
      atTop (nhds 0) := by
    apply hupperRaw.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hy)]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (g := fun y : ℝ ↦ 3 * (|2 * Real.pi * y|⁻¹ * t⁻¹))
  · filter_upwards with y
    exact norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simpa only [Real.norm_eq_abs] using!
      (abs_dirichletSineLimit_sub_sineIntegralTruncation_le
      (2 * Real.pi * y) t
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hy.ne') ht)
  · exact hupper

/-- The compact correction is the full finite Dirichlet integral minus
the compact cutoff quotient.  Every integral here is over a finite interval,
so this is ordinary interval-integral algebra rather than a PV manipulation. -/
theorem compactCutoffPairedSine_smoothCorrection_eq
    (t δ y : ℝ) :
    compactCutoffPairedSine (fixedAwaySmoothCorrection t δ) t y =
      sineIntegralTruncation (2 * Real.pi * y) t -
        ∫ v in (0 : ℝ)..t,
          fixedAwaySmoothCutoff t δ v *
            sineKernel (2 * Real.pi * y) v := by
  have hbase : IntervalIntegrable
      (sineKernel (2 * Real.pi * y)) volume (0 : ℝ) t :=
    (show Continuous (sineKernel (2 * Real.pi * y)) by
      unfold sineKernel
      fun_prop).intervalIntegrable 0 t
  have hcut : IntervalIntegrable
      (fun v : ℝ ↦ fixedAwaySmoothCutoff t δ v *
        sineKernel (2 * Real.pi * y) v) volume (0 : ℝ) t :=
    ((fixedAwaySmoothCutoff_contDiff
      (m := (⊤ : ℕ∞)) t δ).continuous.mul
        (show Continuous (sineKernel (2 * Real.pi * y)) by
          unfold sineKernel
          fun_prop)).intervalIntegrable 0 t
  unfold compactCutoffPairedSine fixedAwaySmoothCorrection
  rw [sineIntegralTruncation]
  rw [← intervalIntegral.integral_sub hbase hcut]
  apply intervalIntegral.integral_congr
  intro v _hv
  unfold sineKernel
  ring

/-- Exact positive-frequency decomposition of `Rχ` into a quantitative
Dirichlet tail and an ordinary compact Fourier sine integral. -/
theorem fixedAwayPVTransform_smooth_eq_tail_add
    {t δ y : ℝ} (hy : 0 < y) :
    fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y =
      (-2 * Complex.I) *
        (((dirichletSineLimit (2 * Real.pi * y) -
          sineIntegralTruncation (2 * Real.pi * y) t) +
          ∫ v in (0 : ℝ)..t,
            fixedAwaySmoothCutoff t δ v *
              sineKernel (2 * Real.pi * y) v : ℝ) : ℂ) := by
  have hsigned : signedExponentialPV y =
      (-2 * Complex.I) *
        (dirichletSineLimit (2 * Real.pi * y) : ℂ) := by
    have ha : 0 < 2 * Real.pi * y :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) hy
    rw [signedExponentialPV, if_pos hy,
      dirichletSineLimit, if_pos ha]
    push_cast
    ring
  rw [fixedAwayPVTransform, compactCutoffPVCorrection,
    compactCutoffPairedSine_smoothCorrection_eq, hsigned]
  push_cast
  ring

/-- The fixed-away PV multiplier for the explicit smooth cutoff vanishes at
positive infinity. -/
theorem tendsto_fixedAwayPVTransform_smooth_atTop_zero
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    Tendsto
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t)
      atTop (nhds 0) := by
  have htail :=
    tendsto_dirichletSineLimit_sub_sineIntegralTruncation_atTop
      (t := t) (hδ.trans hδt)
  have hcut := tendsto_integral_fixedAwayCutoff_sine_atTop hδ hδt
  have hsum : Tendsto
      (fun y : ℝ ↦
        (dirichletSineLimit (2 * Real.pi * y) -
          sineIntegralTruncation (2 * Real.pi * y) t) +
        ∫ v in (0 : ℝ)..t,
          fixedAwaySmoothCutoff t δ v *
            sineKernel (2 * Real.pi * y) v)
      atTop (nhds 0) := by
    simpa only [zero_add] using! htail.add hcut
  have hcast : Tendsto
      (fun y : ℝ ↦ (((dirichletSineLimit (2 * Real.pi * y) -
          sineIntegralTruncation (2 * Real.pi * y) t) +
        ∫ v in (0 : ℝ)..t,
          fixedAwaySmoothCutoff t δ v *
            sineKernel (2 * Real.pi * y) v : ℝ) : ℂ))
      atTop (nhds 0) := by
    exact Complex.ofRealCLM.continuous.continuousAt.tendsto.comp hsum
  have hrhs : Tendsto
      (fun y : ℝ ↦ (-2 * Complex.I) *
        (((dirichletSineLimit (2 * Real.pi * y) -
          sineIntegralTruncation (2 * Real.pi * y) t) +
        ∫ v in (0 : ℝ)..t,
          fixedAwaySmoothCutoff t δ v *
            sineKernel (2 * Real.pi * y) v : ℝ) : ℂ))
      atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hcast
  apply hrhs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact (fixedAwayPVTransform_smooth_eq_tail_add hy).symm

/-- The negative-frequency limit follows from the exact odd/Hermitian
symmetry, with no second oscillatory estimate. -/
theorem tendsto_fixedAwayPVTransform_smooth_atBot_zero
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    Tendsto
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t)
      atBot (nhds 0) := by
  have htop := tendsto_fixedAwayPVTransform_smooth_atTop_zero hδ hδt
  have hneg := (htop.comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_apply, fixedAwayPVTransform_neg, neg_neg,
    neg_zero]
    using! hneg

/-- Pointwise derivative identity, restated for direct use together with the
at-infinity boundary condition proved above. -/
theorem deriv_fixedAwayPVTransform_smooth_eq_fourier
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hy : y ≠ 0) :
    deriv (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y =
      (2 * Real.pi * Complex.I) *
        FourierTransform.fourier
          (realCutoffComplex (fixedAwaySmoothCorrection t δ)) y := by
  exact (hasDerivAt_fixedAwayPVTransform_smooth_eq_fourier
    hδ hδt hy).deriv

/-- Arbitrary-order polynomial decay bound for the derivative of the
fixed-away multiplier.  The right side is the explicit `L¹` mass of the
corresponding compact-correction derivative. -/
theorem fixedAwayPVTransform_smooth_deriv_polynomial
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (n : ℕ) (y : ℝ) (hy : y ≠ 0) :
    (2 * Real.pi * |y|) ^ n *
        ‖deriv
          (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y‖ ≤
      (2 * Real.pi) *
        fixedAwayCorrectionDerivL1
          (fixedAwaySmoothCorrection t δ) n := by
  have hfour := fixedAwaySmoothCorrection_fourier_polynomial
    hδ hδt n y
  rw [deriv_fixedAwayPVTransform_smooth_eq_fourier hδ hδt hy]
  calc
    (2 * Real.pi * |y|) ^ n *
        ‖(2 * Real.pi * Complex.I) *
          FourierTransform.fourier
            (realCutoffComplex (fixedAwaySmoothCorrection t δ)) y‖ =
      (2 * Real.pi) *
        ((2 * Real.pi * |y|) ^ n *
          ‖FourierTransform.fourier
            (realCutoffComplex (fixedAwaySmoothCorrection t δ)) y‖) := by
        simp only [norm_mul, Complex.norm_real, Complex.norm_I,
          Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg,
          mul_one]
        norm_num
        ring
    _ ≤ (2 * Real.pi) *
        fixedAwayCorrectionDerivL1
          (fixedAwaySmoothCorrection t δ) n := by
      exact mul_le_mul_of_nonneg_left hfour
        (mul_nonneg (by norm_num) Real.pi_nonneg)

end

end Erdos1002
