import ErdosProblems.Erdos520.HarperFejerSmoothing
import ErdosProblems.Erdos520.HarperFejerCDFDensity
import ErdosProblems.Erdos520.HarperBlockFirstMoment
import ErdosProblems.Erdos520.HarperSmoothCDFSwap
import ErdosProblems.Erdos520.HarperFejerCharacteristicSwap
import Mathlib.MeasureTheory.Group.IntegralConvolution

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators Interval FourierTransform Real

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Exact Fejér inversion for smoothed distribution functions

This file discharges the inversion identity isolated in
`HarperFejerSmoothing`.  The proof first obtains the inverse transform of the
scaled triangular profile from the already-proved unscaled Fejér transform,
then integrates that density and applies Fubini.
-/

/-- The density of the bandwidth-`T` Fejér law when `T > 0`. -/
noncomputable def harperFejerScaledDensity (T x : ℝ) : ℝ :=
  T * harperFejerDensity (T * x)

theorem harperFejerScaledDensity_nonneg
    {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    0 ≤ harperFejerScaledDensity T x := by
  unfold harperFejerScaledDensity
  exact mul_nonneg hT (harperFejerDensity_nonneg _)

/-- Fourier inversion of the scaled triangular profile, in the characteristic
function normalization used by `harperFejerCDFInversionIntegrand`. -/
theorem integral_exp_neg_mul_harperFejerTriangle_scaled
    {T : ℝ} (hT : 0 < T) (s : ℝ) :
    ((((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ t in Icc (-T) T,
          Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I) *
            (harperFejerTriangle (T⁻¹ * t) : ℂ)) =
      (harperFejerScaledDensity T s : ℂ) := by
  let p : ℝ := 2 * Real.pi * T
  let c : ℝ := p⁻¹
  let g : ℝ → ℂ := fun xi ↦
    Complex.exp
        ((((2 * Real.pi * inner ℝ xi (-(T * s)) : ℝ) : ℂ) *
          Complex.I)) *
      harperFejerFourierProfile xi
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hInv : (∫ xi : ℝ, g xi) = (harperFejerDensity (T * s) : ℂ) := by
    have h := harperFejerFourierInv_eq_density (-(T * s))
    rw [Real.fourierInv_eq'] at h
    simp only [smul_eq_mul] at h
    rw [harperFejerDensity_neg] at h
    exact h
  let f : ℝ → ℂ := fun t ↦
    Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I) *
      (harperFejerTriangle (T⁻¹ * t) : ℂ)
  have hgc : ∀ t : ℝ, g (c * t) = f t := by
    intro t
    have hphase :
        2 * Real.pi * inner ℝ (c * t) (-(T * s)) = -t * s := by
      change 2 * Real.pi * (-(T * s) * (c * t)) = -t * s
      dsimp [c, p]
      field_simp [Real.pi_ne_zero, hT.ne']
    have hprofile : 2 * Real.pi * (c * t) = T⁻¹ * t := by
      dsimp [c, p]
      field_simp [Real.pi_ne_zero, hT.ne']
    unfold g f harperFejerFourierProfile
    rw [hphase, hprofile]
  have hscale : (∫ t : ℝ, f t) =
      (p : ℝ) • ∫ xi : ℝ, g xi := by
    calc
      (∫ t : ℝ, f t) = ∫ t : ℝ, g (c * t) := by
        apply integral_congr_ae
        exact ae_of_all _ fun t ↦ (hgc t).symm
      _ = |c⁻¹| • ∫ xi : ℝ, g xi :=
        Measure.integral_comp_mul_left g c
      _ = (p : ℝ) • ∫ xi : ℝ, g xi := by
        have hcInv : c⁻¹ = p := by simp [c]
        rw [hcInv, abs_of_pos hp]
  have hsupport : Function.support f ⊆ Icc (-T) T := by
    intro t ht
    by_contra htIcc
    have htCases : t < -T ∨ T < t := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using! htIcc
    have htAbs : T < |t| := by
      rcases htCases with htLeft | htRight
      · have htNeg : t < 0 := htLeft.trans (neg_lt_zero.mpr hT)
        rw [abs_of_neg htNeg]
        linarith
      · have htPos : 0 < t := hT.trans htRight
        rw [abs_of_pos htPos]
        exact htRight
    have harg : 1 < |T⁻¹ * t| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hT)]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hT).2 (by simpa using! htAbs)
    have htri : harperFejerTriangle (T⁻¹ * t) = 0 := by
      unfold harperFejerTriangle
      exact max_eq_right (by linarith)
    exact ht (by simp [f, htri])
  have hset : (∫ t in Icc (-T) T, f t) = ∫ t : ℝ, f t := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1
    funext t
    by_cases ht : t ∈ Icc (-T) T
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      by_contra hne
      exact ht (hsupport (fun hf ↦ hne hf.symm))
  rw [show (∫ t in Icc (-T) T,
      Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I) *
        (harperFejerTriangle (T⁻¹ * t) : ℂ)) =
      ∫ t in Icc (-T) T, f t by rfl,
    hset, hscale, hInv]
  unfold harperFejerScaledDensity
  push_cast
  dsimp [p]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Elementary antiderivative used after the Fejér density inversion and
Fubini swap. -/
theorem intervalIntegral_exp_neg_mul_I
    {t : ℝ} (ht : t ≠ 0) (a b : ℝ) :
    (∫ s in a..b, Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I)) =
      (Complex.exp (((-t * b : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-t * a : ℝ) : ℂ) * Complex.I)) /
          (-((t : ℂ) * Complex.I)) := by
  have hc : -((t : ℂ) * Complex.I) ≠ 0 := by
    simp [ht]
  calc
    (∫ s in a..b, Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I)) =
        ∫ s in a..b, Complex.exp (-((t : ℂ) * Complex.I) * (s : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      apply congrArg Complex.exp
      push_cast
      ring_nf
    _ = (Complex.exp (-((t : ℂ) * Complex.I) * (b : ℂ)) -
          Complex.exp (-((t : ℂ) * Complex.I) * (a : ℂ))) /
            (-((t : ℂ) * Complex.I)) :=
      integral_exp_mul_complex hc
    _ = _ := by
      congr 2 <;> push_cast <;> ring_nf

/-- The increment of the scaled Fejér CDF as a compactly supported Fourier
integral.  The value at frequency zero is immaterial and is filled by zero. -/
theorem cdf_harperFejerMeasureScaled_sub_eq_fourier
    {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    (((cdf (harperFejerMeasureScaled T) b -
        cdf (harperFejerMeasureScaled T) a : ℝ) : ℂ)) =
      ((((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ t in Icc (-T) T,
          if t = 0 then 0 else
            (Complex.exp (((-t * b : ℝ) : ℂ) * Complex.I) -
                Complex.exp (((-t * a : ℝ) : ℂ) * Complex.I)) *
              (harperFejerTriangle (T⁻¹ * t) : ℂ) /
                (-((t : ℂ) * Complex.I))) := by
  let F : ℝ → ℝ → ℂ := fun s t ↦
    Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I) *
      (harperFejerTriangle (T⁻¹ * t) : ℂ)
  have hFcont : Continuous (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    apply Continuous.mul
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact Complex.continuous_ofReal.comp
        (continuous_harperFejerTriangle.comp (by fun_prop))
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc a b)).prod
        (volume.restrict (Icc (-T) T))) := by
    rw [Measure.prod_restrict]
    have hcompact : IsCompact (uIcc a b ×ˢ Icc (-T) T) :=
      isCompact_uIcc.prod isCompact_Icc
    refine (hFcont.continuousOn.integrableOn_compact
      hcompact).mono_set ?_
    exact prod_mono uIoc_subset_uIcc (Subset.rfl)
  have hswap :
      (∫ s in a..b, ∫ t in Icc (-T) T, F s t) =
        ∫ t in Icc (-T) T, ∫ s in a..b, F s t := by
    exact intervalIntegral_integral_swap hFint
  rw [cdf_harperFejerMeasureScaled_sub_eq_intervalIntegral hT]
  rw [← intervalIntegral.integral_ofReal]
  calc
    (∫ s in a..b, ((T * harperFejerDensity (T * s) : ℝ) : ℂ)) =
        ∫ s in a..b,
          (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * ∫ t in Icc (-T) T, F s t := by
      apply intervalIntegral.integral_congr
      intro s _hs
      exact (integral_exp_neg_mul_harperFejerTriangle_scaled hT s).symm
    _ = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ s in a..b, ∫ t in Icc (-T) T, F s t := by
      exact intervalIntegral.integral_const_mul
        ((((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ))
        (fun s ↦ ∫ t in Icc (-T) T, F s t)
    _ = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
        ∫ t in Icc (-T) T, ∫ s in a..b, F s t := by rw [hswap]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with t ht
      rw [if_neg ht]
      dsimp [F]
      rw [show (∫ s in a..b,
          Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I) *
            (harperFejerTriangle (T⁻¹ * t) : ℂ)) =
          (∫ s in a..b,
            Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I)) *
              (harperFejerTriangle (T⁻¹ * t) : ℂ) by
            exact intervalIntegral.integral_mul_const
              (harperFejerTriangle (T⁻¹ * t) : ℂ)
              (fun s ↦ Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I)),
        intervalIntegral_exp_neg_mul_I ht]
      field_simp

/-- A difference of translated kernel CDF averages can be put over the
product coupling.  This is the form in which the removable Fourier
singularity is controlled by `|z - w|`. -/
theorem integral_cdf_sub_sub_eq_integral_prod
    (mu nu kappa : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure kappa] (x : ℝ) :
    (∫ z, cdf kappa (x - z) ∂mu) - (∫ w, cdf kappa (x - w) ∂nu) =
      ∫ p, (cdf kappa (x - p.1) - cdf kappa (x - p.2))
        ∂(mu.prod nu) := by
  let H : ℝ → ℝ := fun z ↦ cdf kappa (x - z)
  have hHmeas : Measurable H :=
    (monotone_cdf kappa).measurable.comp (measurable_const.sub measurable_id)
  have hHmu : Integrable H mu := by
    refine (integrable_const (μ := mu) (1 : ℝ)).mono'
      hHmeas.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg kappa (x - z))]
    exact cdf_le_one kappa (x - z)
  have hHnu : Integrable H nu := by
    refine (integrable_const (μ := nu) (1 : ℝ)).mono'
      hHmeas.aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg kappa (x - z))]
    exact cdf_le_one kappa (x - z)
  change (∫ z, H z ∂mu) - (∫ w, H w ∂nu) =
    ∫ p, H p.1 - H p.2 ∂(mu.prod nu)
  rw [integral_sub (hHmu.comp_fst nu) (hHnu.comp_snd mu),
    integral_fun_fst, integral_fun_snd]
  simp

/-- The coupled translated-CDF Fourier kernel.  Coupling the two laws before
dividing by frequency exposes the first-moment domination. -/
noncomputable def harperFejerCoupledKernel
    (T x : ℝ) (p : ℝ × ℝ) (t : ℝ) : ℂ :=
  if t = 0 then 0 else
    (Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) *
      (harperFejerTriangle (T⁻¹ * t) : ℂ) /
        (-((t : ℂ) * Complex.I))

/-- The removable quotient in the coupled kernel is bounded by the distance
between the coupled spatial points. -/
theorem norm_harperFejerCoupledKernel_le
    (T x : ℝ) (p : ℝ × ℝ) (t : ℝ) :
    ‖harperFejerCoupledKernel T x p t‖ ≤ |p.1 - p.2| := by
  by_cases ht : t = 0
  · simp [harperFejerCoupledKernel, ht]
  have hIntBound :
      ‖∫ s in (x - p.2)..(x - p.1),
          Complex.exp (((-t * s : ℝ) : ℂ) * Complex.I)‖ ≤
        1 * |(x - p.1) - (x - p.2)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s _hs
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [intervalIntegral_exp_neg_mul_I ht] at hIntBound
  have hquot :
      ‖(Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) /
            (-((t : ℂ) * Complex.I))‖ ≤ |p.1 - p.2| := by
    calc
      ‖(Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) /
            (-((t : ℂ) * Complex.I))‖ ≤
          |(x - p.1) - (x - p.2)| := by
        simpa only [one_mul] using! hIntBound
      _ = |p.2 - p.1| := by
        congr 1
        ring
      _ = |p.1 - p.2| := abs_sub_comm p.2 p.1
  have htri0 : 0 ≤ harperFejerTriangle (T⁻¹ * t) :=
    harperFejerTriangle_nonneg _
  have htri1 : harperFejerTriangle (T⁻¹ * t) ≤ 1 :=
    harperFejerTriangle_le_one _
  rw [harperFejerCoupledKernel, if_neg ht]
  rw [show
      (Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) *
            (harperFejerTriangle (T⁻¹ * t) : ℂ) /
              (-((t : ℂ) * Complex.I)) =
        ((Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) /
            (-((t : ℂ) * Complex.I))) *
              (harperFejerTriangle (T⁻¹ * t) : ℂ) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htri0]
  calc
    ‖(Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) /
            (-((t : ℂ) * Complex.I))‖ *
        harperFejerTriangle (T⁻¹ * t) ≤ |p.1 - p.2| * 1 := by
      exact mul_le_mul hquot htri1 htri0 (abs_nonneg _)
    _ = |p.1 - p.2| := mul_one _

/-- Absolute integrability of the coupled kernel on a finite frequency
window follows from the two first moments. -/
theorem integrable_harperFejerCoupledKernel
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable id mu) (hnu : Integrable id nu)
    (T x : ℝ) :
    Integrable (Function.uncurry (harperFejerCoupledKernel T x))
      ((mu.prod nu).prod (volume.restrict (Icc (-T) T))) := by
  have hkernelMeas : Measurable
      (Function.uncurry (harperFejerCoupledKernel T x)) := by
    have htri : Measurable (fun q : (ℝ × ℝ) × ℝ ↦
        (harperFejerTriangle (T⁻¹ * q.2) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (continuous_harperFejerTriangle.measurable.comp (by fun_prop))
    unfold Function.uncurry harperFejerCoupledKernel
    apply Measurable.ite
      (by
        simpa only [mem_singleton_iff] using!
          measurable_snd (measurableSet_singleton (0 : ℝ)))
      measurable_const
    exact (((Complex.measurable_exp.comp (by fun_prop)).sub
      (Complex.measurable_exp.comp (by fun_prop))).mul htri).div (by fun_prop)
  have hdom : Integrable (fun q : (ℝ × ℝ) × ℝ ↦
      |q.1.1 - q.1.2|)
      ((mu.prod nu).prod (volume.restrict (Icc (-T) T))) :=
    (Integrable.abs_fst_sub_snd_prod hmu hnu).comp_fst
      (volume.restrict (Icc (-T) T))
  exact hdom.mono' hkernelMeas.aestronglyMeasurable
    (ae_of_all _ fun q ↦ norm_harperFejerCoupledKernel_le T x q.1 q.2)

/-- Exact Fejér-smoothed CDF inversion for probability laws with finite
first moments.  This is the analytic statement formerly isolated as a
conditional premise in `HarperFejerSmoothing`. -/
theorem harperFejerSmoothedCDFIdentity_of_integrable_id
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : Integrable id mu) (hnu : Integrable id nu)
    {T : ℝ} (hT : 0 < T) :
    HarperFejerSmoothedCDFIdentity mu nu T := by
  intro x
  rw [harperSmooth_cdf_eq_integral_cdf_sub mu
      (harperFejerMeasureScaled T) x,
    harperSmooth_cdf_eq_integral_cdf_sub nu
      (harperFejerMeasureScaled T) x,
    integral_cdf_sub_sub_eq_integral_prod mu nu
      (harperFejerMeasureScaled T) x]
  let c : ℂ := (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)
  have hpoint (p : ℝ × ℝ) :
      ((cdf (harperFejerMeasureScaled T) (x - p.1) -
          cdf (harperFejerMeasureScaled T) (x - p.2) : ℝ) : ℂ) =
        c * ∫ t in Icc (-T) T, harperFejerCoupledKernel T x p t := by
    simpa only [c, harperFejerCoupledKernel] using!
      cdf_harperFejerMeasureScaled_sub_eq_fourier hT
        (x - p.2) (x - p.1)
  have hKint := integrable_harperFejerCoupledKernel
    mu nu hmu hnu T x
  have hswap :
      (∫ p : ℝ × ℝ, (∫ t in Icc (-T) T,
          harperFejerCoupledKernel T x p t) ∂(mu.prod nu)) =
        ∫ t in Icc (-T) T, ∫ p : ℝ × ℝ,
          harperFejerCoupledKernel T x p t ∂(mu.prod nu) := by
    exact integral_integral_swap hKint
  have hinner (t : ℝ) :
      (∫ p : ℝ × ℝ, harperFejerCoupledKernel T x p t
          ∂(mu.prod nu)) =
        harperFejerCDFInversionIntegrand
          (charFun mu) (charFun nu) T x t := by
    by_cases ht : t = 0
    · simp [harperFejerCoupledKernel,
        harperFejerCDFInversionIntegrand, ht]
    let r : ℂ := (harperFejerTriangle (T⁻¹ * t) : ℂ) /
      (-((t : ℂ) * Complex.I))
    calc
      (∫ p : ℝ × ℝ, harperFejerCoupledKernel T x p t
          ∂(mu.prod nu)) =
          ∫ p : ℝ × ℝ,
            (Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I)) * r
              ∂(mu.prod nu) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [harperFejerCoupledKernel, if_neg ht]
        dsimp [r]
        ring
      _ = (∫ p : ℝ × ℝ,
            (Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
              Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I))
              ∂(mu.prod nu)) * r := by
        exact integral_mul_const r _
      _ = (Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
            (charFun mu t - charFun nu t)) * r := by
        rw [integral_prod_exp_neg_translate_sub_eq_charFun_sub]
      _ = harperFejerCDFInversionIntegrand
          (charFun mu) (charFun nu) T x t := by
        rw [harperFejerCDFInversionIntegrand, if_neg ht]
        dsimp [r]
        ring
  calc
    (((∫ p : ℝ × ℝ,
      (cdf (harperFejerMeasureScaled T) (x - p.1) -
        cdf (harperFejerMeasureScaled T) (x - p.2) : ℝ)
        ∂(mu.prod nu)) : ℝ) : ℂ) =
        ∫ p : ℝ × ℝ,
      ((cdf (harperFejerMeasureScaled T) (x - p.1) -
        cdf (harperFejerMeasureScaled T) (x - p.2) : ℝ) : ℂ)
          ∂(mu.prod nu) := by
      exact (@integral_ofReal (ℝ × ℝ) _ (mu.prod nu) ℂ _
        (fun p ↦ cdf (harperFejerMeasureScaled T) (x - p.1) -
          cdf (harperFejerMeasureScaled T) (x - p.2))).symm
    _ = ∫ p : ℝ × ℝ,
          c * (∫ t in Icc (-T) T,
            harperFejerCoupledKernel T x p t) ∂(mu.prod nu) := by
      apply integral_congr_ae
      filter_upwards with p
      exact hpoint p
    _ = c * (∫ p : ℝ × ℝ, (∫ t in Icc (-T) T,
          harperFejerCoupledKernel T x p t) ∂(mu.prod nu)) := by
      exact integral_const_mul c _
    _ = c * (∫ t in Icc (-T) T, ∫ p : ℝ × ℝ,
          harperFejerCoupledKernel T x p t ∂(mu.prod nu)) := by
      rw [hswap]
    _ = c * ∫ t in Icc (-T) T,
          harperFejerCDFInversionIntegrand
            (charFun mu) (charFun nu) T x t := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact hinner t
    _ = _ := rfl

end Problem520
end Erdos
