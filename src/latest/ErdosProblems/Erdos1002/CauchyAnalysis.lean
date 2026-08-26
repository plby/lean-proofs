import ErdosProblems.Erdos1002.ProbabilityFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Analytic facts about the limiting Cauchy law

We identify the limiting Stieltjes measure with its exact density and
compute its characteristic function.  The Fourier calculation starts from
the elementary pair `exp (-|x|)` and `2 / (1 + (2πx)^2)` and uses mathlib's
Fourier inversion theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology

namespace Erdos1002

noncomputable section

/-- The exact Lebesgue density of the centered Cauchy law of scale `1 / (2π)`. -/
def cauchyLimitDensity (x : ℝ) : ℝ :=
  2 / (1 + (2 * Real.pi * x) ^ 2)

/-- The elementary function whose Fourier transform is `cauchyLimitDensity`. -/
def laplaceKernel (x : ℝ) : ℂ :=
  Real.exp (-|x|)

theorem cauchyLimitDensity_nonneg (x : ℝ) : 0 ≤ cauchyLimitDensity x := by
  unfold cauchyLimitDensity
  positivity

theorem continuous_cauchyLimitDensity : Continuous cauchyLimitDensity := by
  unfold cauchyLimitDensity
  exact continuous_const.div
    (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
    (fun x ↦ by positivity)

theorem continuous_laplaceKernel : Continuous laplaceKernel := by
  unfold laplaceKernel
  fun_prop

theorem integrable_laplaceKernel : Integrable laplaceKernel := by
  have hreal : Integrable (fun x : ℝ ↦ Real.exp (-|x|)) := by
    rw [← integrableOn_univ,
      ← (Iic_union_Ioi : Iic (0 : ℝ) ∪ Ioi 0 = univ), integrableOn_union]
    constructor
    · refine (integrableOn_exp_mul_Iic (a := (1 : ℝ)) zero_lt_one 0).congr_fun ?_
        measurableSet_Iic
      intro x hx
      dsimp only
      rw [abs_of_nonpos (mem_Iic.mp hx)]
      ring_nf
    · refine (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0).congr_fun ?_
        measurableSet_Ioi
      intro x hx
      dsimp only
      rw [abs_of_pos (mem_Ioi.mp hx)]
      ring_nf
  exact hreal.ofReal

theorem integrable_cauchyLimitDensity : Integrable cauchyLimitDensity := by
  have hbase : Integrable (fun x : ℝ ↦ (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hscale : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hcomp := hbase.comp_mul_left' hscale
  have hmul := hcomp.const_mul (2 : ℝ)
  simpa only [cauchyLimitDensity, div_eq_mul_inv] using! hmul

theorem hasDerivAt_cauchyLimitCDF (x : ℝ) :
    HasDerivAt cauchyLimitCDF (cauchyLimitDensity x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ ↦ (2 * Real.pi) * y) (2 * Real.pi) x := by
    simpa using! (hasDerivAt_id x).const_mul (2 * Real.pi)
  have hatan := (Real.hasDerivAt_arctan (2 * Real.pi * x)).comp x hinner
  have hscale := hatan.const_mul (1 / Real.pi)
  have hadd := hscale.const_add ((1 : ℝ) / 2)
  unfold cauchyLimitCDF cauchyLimitDensity
  convert! hadd using 1
  field_simp [Real.pi_ne_zero]

theorem integral_Iic_cauchyLimitDensity (c : ℝ) :
    ∫ x : ℝ in Iic c, cauchyLimitDensity x = cauchyLimitCDF c := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := c) (m := (0 : ℝ))
    (fun (x : ℝ) (_hx : x ∈ Iic c) ↦ hasDerivAt_cauchyLimitCDF x)
    integrable_cauchyLimitDensity.integrableOn tendsto_cauchyLimitCDF_atBot
  simpa using! h

/-- The measure obtained directly from the exact Cauchy density. -/
def cauchyLimitDensityMeasure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (cauchyLimitDensity x))

/-- The Stieltjes construction in `ProbabilityFoundations` is exactly the
Lebesgue measure with density `cauchyLimitDensity`. -/
theorem cauchyLimitMeasure_eq_withDensity :
    cauchyLimitMeasure = cauchyLimitDensityMeasure := by
  apply Measure.ext_of_Iic
  intro c
  rw [cauchyLimitMeasure, StieltjesFunction.measure_Iic
    cauchyLimitStieltjes tendsto_cauchyLimitCDF_atBot]
  change ENNReal.ofReal (cauchyLimitCDF c - 0) = _
  rw [sub_zero, cauchyLimitDensityMeasure, withDensity_apply _ measurableSet_Iic]
  rw [← ofReal_integral_eq_lintegral_ofReal
    integrable_cauchyLimitDensity.integrableOn
    (Filter.Eventually.of_forall (fun x ↦ cauchyLimitDensity_nonneg x))]
  rw [integral_Iic_cauchyLimitDensity]

private theorem integrable_fourier_laplaceKernel_integrand (w : ℝ) :
    Integrable (fun x : ℝ ↦
      Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) * laplaceKernel x) := by
  refine integrable_laplaceKernel.bdd_mul (c := 1) (by fun_prop) ?_
  filter_upwards with x
  rw [Complex.norm_exp]
  simp

/-- The elementary Fourier pair underlying the limiting Cauchy law. -/
theorem fourier_laplaceKernel (w : ℝ) :
    FourierTransform.fourier laplaceKernel w = (cauchyLimitDensity w : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_add_compl measurableSet_Iic
    (integrable_fourier_laplaceKernel_integrand w), compl_Iic]
  have hIic :
      (∫ x : ℝ in Iic 0,
        Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) * laplaceKernel x) =
        ∫ x : ℝ in Iic 0,
          Complex.exp (((1 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I) * x) := by
    refine setIntegral_congr_fun measurableSet_Iic ?_
    intro x hx
    simp only [laplaceKernel, abs_of_nonpos (mem_Iic.mp hx), neg_neg,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hIoi :
      (∫ x : ℝ in Ioi 0,
        Complex.exp ((-2 * Real.pi * x * w : ℝ) * Complex.I) * laplaceKernel x) =
        ∫ x : ℝ in Ioi 0,
          Complex.exp (((-1 : ℂ) - (2 * Real.pi * w : ℝ) * Complex.I) * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    simp only [laplaceKernel, abs_of_pos (mem_Ioi.mp hx),
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hIic, hIoi]
  rw [integral_exp_mul_complex_Iic (by simp),
    integral_exp_mul_complex_Ioi (by simp)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div]
  unfold cauchyLimitDensity
  push_cast
  have hleft' :
      (1 - (Real.pi : ℂ) * (w : ℂ) * Complex.I * 2) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hright' :
      (-1 - (Real.pi : ℂ) * (w : ℂ) * Complex.I * 2) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hdenom' :
      (1 + (Real.pi : ℂ) ^ 2 * (w : ℂ) ^ 2 * 4) ≠ 0 := by
    exact_mod_cast
      (by positivity : (1 + Real.pi ^ 2 * w ^ 2 * 4 : ℝ) ≠ 0)
  ring_nf
  rw [inv_sub_inv hleft' hright']
  field_simp [hdenom']
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_cauchyLimitDensity_complex :
    Integrable (fun x : ℝ ↦ (cauchyLimitDensity x : ℂ)) :=
  integrable_cauchyLimitDensity.ofReal

/-- Fourier inversion gives the transform in the opposite direction. -/
theorem fourier_cauchyLimitDensity (w : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ (cauchyLimitDensity x : ℂ)) w =
      laplaceKernel w := by
  have hpair :
      FourierTransform.fourier laplaceKernel =
        (fun x : ℝ ↦ (cauchyLimitDensity x : ℂ)) :=
    funext fourier_laplaceKernel
  have hfourierInt : Integrable (FourierTransform.fourier laplaceKernel) := by
    rw [hpair]
    exact integrable_cauchyLimitDensity_complex
  have hinversion := continuous_laplaceKernel.fourierInv_fourier_eq
    integrable_laplaceKernel hfourierInt
  have hat := congrFun hinversion (-w)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at hat
  rw [← hpair]
  calc
    FourierTransform.fourier (FourierTransform.fourier laplaceKernel) w =
        laplaceKernel (-w) := hat
    _ = laplaceKernel w := by simp [laplaceKernel]

theorem charFun_cauchyLimitDensityMeasure_eq_fourier (t : ℝ) :
    charFun cauchyLimitDensityMeasure t =
      FourierTransform.fourier
        (fun x : ℝ ↦ (cauchyLimitDensity x : ℂ))
        (-t / (2 * Real.pi)) := by
  rw [charFun_apply_real, cauchyLimitDensityMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    continuous_cauchyLimitDensity.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (cauchyLimitDensity_nonneg x)]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [mul_comm (cauchyLimitDensity x : ℂ)]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The characteristic function of the exact density has the Cauchy exponent. -/
theorem charFun_cauchyLimitDensityMeasure (t : ℝ) :
    charFun cauchyLimitDensityMeasure t =
      Complex.exp (-(|t| / (2 * Real.pi) : ℝ)) := by
  rw [charFun_cauchyLimitDensityMeasure_eq_fourier,
    fourier_cauchyLimitDensity]
  unfold laplaceKernel
  rw [abs_div, abs_neg, abs_of_pos (mul_pos (by positivity) Real.pi_pos)]
  rw [Complex.ofReal_exp]
  norm_cast

/-- The limiting Stieltjes Cauchy law has characteristic function
`exp (-|t| / (2π))`, with exactly the manuscript's scale. -/
theorem charFun_cauchyLimitMeasure (t : ℝ) :
    charFun cauchyLimitMeasure t =
      Complex.exp (-(|t| / (2 * Real.pi) : ℝ)) := by
  rw [cauchyLimitMeasure_eq_withDensity]
  exact charFun_cauchyLimitDensityMeasure t

theorem charFun_cauchyLimitProbability (t : ℝ) :
    charFun (cauchyLimitProbability : Measure ℝ) t =
      Complex.exp (-(|t| / (2 * Real.pi) : ℝ)) := by
  change charFun cauchyLimitMeasure t = _
  exact charFun_cauchyLimitMeasure t

end

end Erdos1002
