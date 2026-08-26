import ErdosProblems.Erdos1002.FixedAwayPVAtInfinity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Integrable derivative and tail bounds for the fixed-away PV multiplier

The fixed-away multiplier has a jump at zero, so all differential arguments
are made on the two open half-lines.  The zeroth- and second-order Fourier
bounds give one global Cauchy envelope for its classical derivative (the
single exceptional point is harmless).  This yields integrability, the exact
FTC tail representation on each half-line, and an explicit reciprocal tail
bound for the multiplier itself.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

def fixedAwayDerivativeBound0 (t δ : ℝ) : ℝ :=
  (2 * Real.pi) *
    fixedAwayCorrectionDerivL1 (fixedAwaySmoothCorrection t δ) 0

def fixedAwayDerivativeBound2 (t δ : ℝ) : ℝ :=
  (2 * Real.pi) *
    fixedAwayCorrectionDerivL1 (fixedAwaySmoothCorrection t δ) 2

def fixedAwayDerivativeBound (t δ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi) *
    fixedAwayCorrectionDerivL1 (fixedAwaySmoothCorrection t δ) n

def fixedAwayDerivativeCauchyConstant (t δ : ℝ) : ℝ :=
  2 * (fixedAwayDerivativeBound0 t δ + fixedAwayDerivativeBound2 t δ)

theorem fixedAwayCorrectionDerivL1_nonneg (κ : ℝ → ℝ) (n : ℕ) :
    0 ≤ fixedAwayCorrectionDerivL1 κ n := by
  unfold fixedAwayCorrectionDerivL1
  exact integral_nonneg fun _x ↦ norm_nonneg _

theorem fixedAwayDerivativeBound0_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayDerivativeBound0 t δ := by
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    (fixedAwayCorrectionDerivL1_nonneg _ 0)

theorem fixedAwayDerivativeBound2_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayDerivativeBound2 t δ := by
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    (fixedAwayCorrectionDerivL1_nonneg _ 2)

theorem fixedAwayDerivativeBound_nonneg (t δ : ℝ) (n : ℕ) :
    0 ≤ fixedAwayDerivativeBound t δ n := by
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    (fixedAwayCorrectionDerivL1_nonneg _ n)

theorem fixedAwayDerivativeCauchyConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayDerivativeCauchyConstant t δ := by
  unfold fixedAwayDerivativeCauchyConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg (fixedAwayDerivativeBound0_nonneg t δ)
      (fixedAwayDerivativeBound2_nonneg t δ))

theorem norm_deriv_fixedAwayPVTransform_smooth_le_cauchyEnvelope
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    {y : ℝ} (hy : y ≠ 0) :
    ‖deriv
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y‖ ≤
      fixedAwayDerivativeCauchyConstant t δ * (1 + y ^ 2)⁻¹ := by
  let D : ℝ := ‖deriv
    (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y‖
  let C0 : ℝ := fixedAwayDerivativeBound0 t δ
  let C2 : ℝ := fixedAwayDerivativeBound2 t δ
  have hD : 0 ≤ D := norm_nonneg _
  have hC0 : 0 ≤ C0 := fixedAwayDerivativeBound0_nonneg t δ
  have hC2 : 0 ≤ C2 := fixedAwayDerivativeBound2_nonneg t δ
  have hzero := fixedAwayPVTransform_smooth_deriv_polynomial
    hδ hδt 0 y hy
  have htwo := fixedAwayPVTransform_smooth_deriv_polynomial
    hδ hδt 2 y hy
  change D ≤ 2 * (C0 + C2) * (1 + y ^ 2)⁻¹
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hden]
  by_cases hySmall : |y| ≤ 1
  · have hysq : y ^ 2 ≤ 1 := by
      rw [← sq_abs]
      simpa only [one_pow] using!
        (sq_le_sq₀ (abs_nonneg y) zero_le_one).2 hySmall
    have hD0 : D ≤ C0 := by
      simpa only [pow_zero, one_mul, D, C0,
        fixedAwayDerivativeBound0] using! hzero
    nlinarith
  · have hyLarge : 1 ≤ y ^ 2 := by
      have : 1 < |y| := lt_of_not_ge hySmall
      nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
    have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hD2 : (2 * Real.pi) ^ 2 * y ^ 2 * D ≤ C2 := by
      calc
        (2 * Real.pi) ^ 2 * y ^ 2 * D =
            (2 * Real.pi * |y|) ^ 2 * D := by
          ring_nf
          rw [sq_abs]
          ring
        _ ≤ C2 := by
          simpa only [D, C2, fixedAwayDerivativeBound2] using! htwo
    have hreduce : y ^ 2 * D ≤ C2 := by
      have hnonneg : 0 ≤ ((2 * Real.pi) ^ 2 - 1) * (y ^ 2 * D) :=
        mul_nonneg (sub_nonneg.mpr hpi) (mul_nonneg (sq_nonneg y) hD)
      nlinarith
    nlinarith

theorem integrable_deriv_fixedAwayPVTransform_smooth
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) :
    Integrable
      (fun y : ℝ ↦ deriv
        (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y) := by
  let K : ℝ := fixedAwayDerivativeCauchyConstant t δ
  let F : ℝ → ℂ := fun y ↦
    FourierTransform.fourier
      (realCutoffComplex (fixedAwaySmoothCorrection t δ)) y
  have hκint : Integrable
      (realCutoffComplex (fixedAwaySmoothCorrection t δ)) :=
    realCutoffComplex_iteratedDeriv_integrable
      (fixedAwaySmoothCorrection t δ)
      (fixedAwaySmoothCorrection_contDiff
        (m := (⊤ : ℕ∞)) t δ)
      (fun x hx ↦ fixedAwaySmoothCorrection_eq_zero_of_le_abs hδ hδt hx) 0
  have hFcont : Continuous F := by
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar continuous_inner hκint
  have hderivMeas : AEStronglyMeasurable
      (fun y : ℝ ↦ deriv
        (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) y) := by
    have hcontinuous : Continuous (fun y : ℝ ↦
        (2 * Real.pi * Complex.I) * F y) :=
      continuous_const.mul hFcont
    apply hcontinuous.aestronglyMeasurable.congr
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with y hy
    exact (deriv_fixedAwayPVTransform_smooth_eq_fourier hδ hδt hy).symm
  have hmajor : Integrable (fun y : ℝ ↦ K * (1 + y ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  apply hmajor.mono' hderivMeas
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with y hy
  exact norm_deriv_fixedAwayPVTransform_smooth_le_cauchyEnvelope
    hδ hδt hy

/-- On the positive half-line the multiplier is the negative tail integral
of its derivative.  The endpoint is strictly positive, so the jump at zero
does not enter the FTC hypothesis. -/
theorem fixedAwayPVTransform_smooth_eq_neg_integral_deriv_Ioi
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ < t) (hy : 0 < y) :
    fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y =
      -∫ u in Ioi y,
        deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) u := by
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := y) (m := (0 : ℂ))
    (f := fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t)
    (f' := fun u ↦ deriv
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u)
    (fun u hu ↦ by
      have hu0 : u ≠ 0 := (hy.trans_le hu).ne'
      have hraw := hasDerivAt_fixedAwayPVTransform_smooth_eq_fourier
        hδ hδt.le hu0
      convert! hraw using 1
      exact deriv_fixedAwayPVTransform_smooth_eq_fourier
        hδ hδt.le hu0)
    ((integrable_deriv_fixedAwayPVTransform_smooth hδ hδt.le).integrableOn)
    (tendsto_fixedAwayPVTransform_smooth_atTop_zero hδ hδt)
  have htail : (∫ u in Ioi y,
      deriv (fixedAwayPVTransform
        (fixedAwaySmoothCorrection t δ) t) u) =
      -fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y := by
    simpa using! hFTC
  rw [htail]
  simp

/-- Second-order Fourier decay rewritten as the reciprocal-square envelope
needed for an integrable positive tail. -/
theorem norm_deriv_fixedAwayPVTransform_smooth_le_inv_sq
    {t δ u : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hu : 0 < u) :
    ‖deriv
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u‖ ≤
      (fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2) *
        u ^ (-2 : ℝ) := by
  have hpoly := fixedAwayPVTransform_smooth_deriv_polynomial
    hδ hδt 2 u hu.ne'
  have hfreq : 0 < (2 * Real.pi * u) ^ 2 := by positivity
  have hfirst :
      ‖deriv
        (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u‖ ≤
        fixedAwayDerivativeBound2 t δ / (2 * Real.pi * u) ^ 2 := by
    apply (le_div_iff₀ hfreq).2
    simpa only [fixedAwayDerivativeBound2, abs_of_pos hu, mul_comm]
      using! hpoly
  calc
    ‖deriv
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u‖ ≤
        fixedAwayDerivativeBound2 t δ / (2 * Real.pi * u) ^ 2 := hfirst
    _ = (fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2) *
        u ^ (-2 : ℝ) := by
      have hrpow : u ^ (-2 : ℝ) = (u ^ 2)⁻¹ := by
        change Real.rpow u (-2) = _
        simpa only [Real.rpow_two] using! (Real.rpow_neg hu.le (2 : ℝ))
      rw [hrpow]
      field_simp [Real.pi_ne_zero, hu.ne']

/-- Arbitrary-order version of the reciprocal derivative bound. -/
theorem norm_deriv_fixedAwayPVTransform_smooth_le_inv_rpow
    {t δ u : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (n : ℕ) (hu : 0 < u) :
    ‖deriv
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u‖ ≤
      (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
        u ^ (-(n : ℝ)) := by
  have hpoly := fixedAwayPVTransform_smooth_deriv_polynomial
    hδ hδt n u hu.ne'
  have hfreq : 0 < (2 * Real.pi * u) ^ n := by positivity
  have hfirst :
      ‖deriv
        (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u‖ ≤
        fixedAwayDerivativeBound t δ n / (2 * Real.pi * u) ^ n := by
    apply (le_div_iff₀ hfreq).2
    simpa only [fixedAwayDerivativeBound, abs_of_pos hu, mul_comm]
      using! hpoly
  calc
    ‖deriv
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t) u‖ ≤
        fixedAwayDerivativeBound t δ n / (2 * Real.pi * u) ^ n := hfirst
    _ = (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
        u ^ (-(n : ℝ)) := by
      have hrpow : u ^ (-(n : ℝ)) = (u ^ n)⁻¹ := by
        have hneg := Real.rpow_neg hu.le (n : ℝ)
        rw [Real.rpow_natCast] at hneg
        exact hneg
      rw [hrpow, mul_pow]
      field_simp [Real.pi_ne_zero, hu.ne']

/-- Every fixed derivative order `n > 1` integrates to a corresponding
polynomial tail for the multiplier itself.  The expression on the right is
the exact elementary integral of `u^{-n}`. -/
theorem norm_fixedAwayPVTransform_smooth_le_rpow_tail
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (n : ℕ) (hn : 1 < n) (hy : 0 < y) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
        (-y ^ (-(n : ℝ) + 1) / (-(n : ℝ) + 1)) := by
  rw [fixedAwayPVTransform_smooth_eq_neg_integral_deriv_Ioi
    hδ hδt hy, norm_neg]
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexp : -(n : ℝ) < -1 := by linarith
  have hrpowInt : IntegrableOn
      (fun u : ℝ ↦ u ^ (-(n : ℝ))) (Ioi y) :=
    integrableOn_Ioi_rpow_of_lt hexp hy
  have hmajor : IntegrableOn
      (fun u : ℝ ↦
        (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
          u ^ (-(n : ℝ))) (Ioi y) :=
    hrpowInt.const_mul _
  calc
    ‖∫ u in Ioi y,
        deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) u‖ ≤
        ∫ u in Ioi y,
          (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
            u ^ (-(n : ℝ)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_deriv_fixedAwayPVTransform_smooth_le_inv_rpow
        hδ hδt.le n (hy.trans hu)
    _ = (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
        (-y ^ (-(n : ℝ) + 1) / (-(n : ℝ) + 1)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (a := -(n : ℝ)) hexp hy]

/-- Symmetric arbitrary fixed-order tail away from the jump. -/
theorem norm_fixedAwayPVTransform_smooth_le_rpow_tail_abs
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (n : ℕ) (hn : 1 < n) (hy : y ≠ 0) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      (fixedAwayDerivativeBound t δ n / (2 * Real.pi) ^ n) *
        (-|y| ^ (-(n : ℝ) + 1) / (-(n : ℝ) + 1)) := by
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have h := norm_fixedAwayPVTransform_smooth_le_rpow_tail
      hδ hδt n hn (neg_pos.mpr hyneg)
    rw [fixedAwayPVTransform_neg, norm_neg] at h
    simpa only [abs_of_neg hyneg] using! h
  · simpa only [abs_of_pos hypos] using!
      (norm_fixedAwayPVTransform_smooth_le_rpow_tail
        hδ hδt n hn hypos)

/-- Explicit reciprocal tail bound on the positive half-line. -/
theorem norm_fixedAwayPVTransform_smooth_le_inv
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ < t) (hy : 0 < y) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      fixedAwayDerivativeBound2 t δ /
        ((2 * Real.pi) ^ 2 * y) := by
  rw [fixedAwayPVTransform_smooth_eq_neg_integral_deriv_Ioi
    hδ hδt hy, norm_neg]
  have hrpowInt : IntegrableOn (fun u : ℝ ↦ u ^ (-2 : ℝ)) (Ioi y) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hy
  have hmajor : IntegrableOn
      (fun u : ℝ ↦
        (fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2) *
          u ^ (-2 : ℝ)) (Ioi y) :=
    hrpowInt.const_mul _
  calc
    ‖∫ u in Ioi y,
        deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) u‖ ≤
        ∫ u in Ioi y,
          (fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2) *
            u ^ (-2 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_deriv_fixedAwayPVTransform_smooth_le_inv_sq
        hδ hδt.le (hy.trans hu)
    _ = fixedAwayDerivativeBound2 t δ /
        ((2 * Real.pi) ^ 2 * y) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) hy]
      norm_num [Real.rpow_neg_one]
      field_simp [Real.pi_ne_zero, hy.ne']

/-- Symmetric reciprocal bound away from the jump. -/
theorem norm_fixedAwayPVTransform_smooth_le_inv_abs
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ < t) (hy : y ≠ 0) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      fixedAwayDerivativeBound2 t δ /
        ((2 * Real.pi) ^ 2 * |y|) := by
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have h := norm_fixedAwayPVTransform_smooth_le_inv
      hδ hδt (neg_pos.mpr hyneg)
    rw [fixedAwayPVTransform_neg, norm_neg] at h
    simpa only [abs_of_neg hyneg] using! h
  · simpa only [abs_of_pos hypos] using!
      (norm_fixedAwayPVTransform_smooth_le_inv hδ hδt hypos)

def fixedAwayPVLocalBound (t : ℝ) : ℝ :=
  Real.pi + 4 * Real.pi * |t|

def fixedAwayPVGlobalDecayConstant (t δ : ℝ) : ℝ :=
  2 * (fixedAwayPVLocalBound t +
    fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2)

theorem fixedAwayPVLocalBound_nonneg (t : ℝ) :
    0 ≤ fixedAwayPVLocalBound t := by
  unfold fixedAwayPVLocalBound
  positivity

theorem fixedAwayPVGlobalDecayConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayPVGlobalDecayConstant t δ := by
  unfold fixedAwayPVGlobalDecayConstant
  have hden : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  exact mul_nonneg (by norm_num) (add_nonneg
    (fixedAwayPVLocalBound_nonneg t)
    (div_nonneg (fixedAwayDerivativeBound2_nonneg t δ) hden))

theorem norm_signedExponentialPV_le_pi (y : ℝ) :
    ‖signedExponentialPV y‖ ≤ Real.pi := by
  unfold signedExponentialPV
  split_ifs <;>
    simp [Complex.norm_real, abs_of_nonneg Real.pi_nonneg,
      Real.pi_nonneg]

theorem norm_fixedAwayPVTransform_smooth_le_local
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hy : |y| ≤ 1) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      fixedAwayPVLocalBound t := by
  have hκ : ∀ v ∈ uIoc (0 : ℝ) t,
      |fixedAwaySmoothCorrection t δ v| ≤ 1 := by
    intro v _hv
    exact abs_fixedAwaySmoothCorrection_le_one hδ hδt v
  have hcorr := norm_compactCutoffPVCorrection_le
    (fixedAwaySmoothCorrection t δ) t y hκ
  have hfreq : |2 * Real.pi * y| ≤ 2 * Real.pi := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg Real.pi_nonneg]
    nlinarith [Real.pi_pos]
  have hcorr' :
      ‖compactCutoffPVCorrection
        (fixedAwaySmoothCorrection t δ) t y‖ ≤
        4 * Real.pi * |t| := by
    calc
      ‖compactCutoffPVCorrection
          (fixedAwaySmoothCorrection t δ) t y‖ ≤
          2 * (((1 : ℝ) * |2 * Real.pi * y|) * |t|) := hcorr
      _ ≤ 2 * ((1 * (2 * Real.pi)) * |t|) := by
        gcongr
      _ = 4 * Real.pi * |t| := by ring
  unfold fixedAwayPVTransform fixedAwayPVLocalBound
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_signedExponentialPV_le_pi y) hcorr')

/-- Global reciprocal envelope, including the bounded jump neighbourhood.
This is the convenient pointwise input for separated scaled products. -/
theorem norm_fixedAwayPVTransform_smooth_le_globalDecay
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (y : ℝ) :
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
      fixedAwayPVGlobalDecayConstant t δ * (1 + |y|)⁻¹ := by
  let D : ℝ := ‖fixedAwayPVTransform
    (fixedAwaySmoothCorrection t δ) t y‖
  let B : ℝ := fixedAwayPVLocalBound t
  let C : ℝ := fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2
  have hD : 0 ≤ D := norm_nonneg _
  have hB : 0 ≤ B := fixedAwayPVLocalBound_nonneg t
  have hC : 0 ≤ C := div_nonneg
    (fixedAwayDerivativeBound2_nonneg t δ) (sq_nonneg _)
  change D ≤ 2 * (B + C) * (1 + |y|)⁻¹
  have hden : 0 < 1 + |y| := by positivity
  rw [le_mul_inv_iff₀ hden]
  by_cases hySmall : |y| ≤ 1
  · have hlocal : D ≤ B := by
      simpa only [D, B] using!
        norm_fixedAwayPVTransform_smooth_le_local hδ hδt.le hySmall
    nlinarith
  · have hyLarge : 1 < |y| := lt_of_not_ge hySmall
    have hy0 : y ≠ 0 := abs_pos.mp (zero_lt_one.trans hyLarge)
    have htail := norm_fixedAwayPVTransform_smooth_le_inv_abs
      hδ hδt hy0
    have htailC : D ≤ C / |y| := by
      dsimp only [D, C]
      calc
        ‖fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t y‖ ≤
            fixedAwayDerivativeBound2 t δ /
              ((2 * Real.pi) ^ 2 * |y|) := htail
        _ = (fixedAwayDerivativeBound2 t δ / (2 * Real.pi) ^ 2) /
            |y| := by ring
    have htail' : D * |y| ≤ C := by
      have habs : 0 < |y| := abs_pos.mpr hy0
      exact (le_div_iff₀ habs).mp htailC
    nlinarith

/-! ## Scaled Hermitian products -/

def fixedAwayScaledPV (t δ s a x : ℝ) : ℂ :=
  fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t ((x - a) / s)

def fixedAwayScaledHermitianProduct
    (t δ s a s' a' x : ℝ) : ℂ :=
  fixedAwayScaledPV t δ s a x *
    conj (fixedAwayScaledPV t δ s' a' x)

theorem hasDerivAt_fixedAwayScaledPV
    {t δ s a x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : s ≠ 0) (hxa : x ≠ a) :
    HasDerivAt (fixedAwayScaledPV t δ s a)
      ((s⁻¹ : ℝ) •
        deriv (fixedAwayPVTransform
          (fixedAwaySmoothCorrection t δ) t) ((x - a) / s)) x := by
  have hu : (x - a) / s ≠ 0 := div_ne_zero (sub_ne_zero.mpr hxa) hs
  have hbase := hasDerivAt_fixedAwayPVTransform_smooth_eq_fourier
    hδ hδt hu
  have hinner : HasDerivAt (fun z : ℝ ↦ (z - a) / s) s⁻¹ x := by
    convert! ((hasDerivAt_id x).sub_const a).div_const s using 1
    simp [one_div]
  have hcomp := hbase.scomp x hinner
  rw [deriv_fixedAwayPVTransform_smooth_eq_fourier hδ hδt hu]
  simpa only [fixedAwayScaledPV, Function.comp_apply] using! hcomp

theorem hasDerivAt_fixedAwayScaledHermitianProduct
    {t δ s a s' a' x : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (hs : s ≠ 0) (hs' : s' ≠ 0) (hxa : x ≠ a) (hxa' : x ≠ a') :
    HasDerivAt (fixedAwayScaledHermitianProduct t δ s a s' a')
      (((s⁻¹ : ℝ) •
          deriv (fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t) ((x - a) / s)) *
        conj (fixedAwayScaledPV t δ s' a' x) +
        fixedAwayScaledPV t δ s a x *
          conj ((s'⁻¹ : ℝ) •
            deriv (fixedAwayPVTransform
              (fixedAwaySmoothCorrection t δ) t) ((x - a') / s'))) x := by
  have hleft := hasDerivAt_fixedAwayScaledPV
    hδ hδt hs hxa
  have hright := hasDerivAt_fixedAwayScaledPV
    hδ hδt hs' hxa'
  have hprod := hleft.mul hright.star
  simpa only [fixedAwayScaledHermitianProduct, Pi.mul_apply,
    starRingEnd_apply] using! hprod

theorem norm_fixedAwayScaledHermitianProduct_le
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x : ℝ) :
    ‖fixedAwayScaledHermitianProduct t δ s a s' a' x‖ ≤
      (fixedAwayPVGlobalDecayConstant t δ *
        (1 + |(x - a) / s|)⁻¹) *
      (fixedAwayPVGlobalDecayConstant t δ *
        (1 + |(x - a') / s'|)⁻¹) := by
  unfold fixedAwayScaledHermitianProduct fixedAwayScaledPV
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul
    (norm_fixedAwayPVTransform_smooth_le_globalDecay hδ hδt _)
    (norm_fixedAwayPVTransform_smooth_le_globalDecay hδ hδt _)
    (norm_nonneg _)
    (mul_nonneg (fixedAwayPVGlobalDecayConstant_nonneg t δ)
      (inv_nonneg.mpr (by positivity)))

/-- Direct pointwise derivative envelope for the scaled Hermitian product.
The only excluded points are its two carrier jumps.  This is the continuous
BV input; those two jumps must be added separately after sampling or cutting
an interval. -/
theorem norm_deriv_fixedAwayScaledHermitianProduct_le
    {t δ s a s' a' x : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : s ≠ 0) (hs' : s' ≠ 0) (hxa : x ≠ a) (hxa' : x ≠ a') :
    ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤
      |s|⁻¹ *
          (fixedAwayDerivativeCauchyConstant t δ *
            (1 + ((x - a) / s) ^ 2)⁻¹) *
          (fixedAwayPVGlobalDecayConstant t δ *
            (1 + |(x - a') / s'|)⁻¹) +
        (fixedAwayPVGlobalDecayConstant t δ *
            (1 + |(x - a) / s|)⁻¹) *
          (|s'|⁻¹ *
            (fixedAwayDerivativeCauchyConstant t δ *
              (1 + ((x - a') / s') ^ 2)⁻¹)) := by
  rw [(hasDerivAt_fixedAwayScaledHermitianProduct
    hδ hδt.le hs hs' hxa hxa').deriv]
  calc
    ‖((s⁻¹ : ℝ) •
          deriv (fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t) ((x - a) / s)) *
        conj (fixedAwayScaledPV t δ s' a' x) +
        fixedAwayScaledPV t δ s a x *
          conj ((s'⁻¹ : ℝ) •
            deriv (fixedAwayPVTransform
              (fixedAwaySmoothCorrection t δ) t) ((x - a') / s'))‖ ≤
      ‖(s⁻¹ : ℝ) •
          deriv (fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t) ((x - a) / s)‖ *
        ‖fixedAwayScaledPV t δ s' a' x‖ +
      ‖fixedAwayScaledPV t δ s a x‖ *
        ‖(s'⁻¹ : ℝ) •
          deriv (fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t) ((x - a') / s')‖ := by
      simpa only [norm_mul, Complex.norm_conj] using! norm_add_le
        (((s⁻¹ : ℝ) •
          deriv (fixedAwayPVTransform
            (fixedAwaySmoothCorrection t δ) t) ((x - a) / s)) *
          conj (fixedAwayScaledPV t δ s' a' x))
        (fixedAwayScaledPV t δ s a x *
          conj ((s'⁻¹ : ℝ) •
            deriv (fixedAwayPVTransform
              (fixedAwaySmoothCorrection t δ) t) ((x - a') / s')))
    _ ≤ |s|⁻¹ *
          (fixedAwayDerivativeCauchyConstant t δ *
            (1 + ((x - a) / s) ^ 2)⁻¹) *
          (fixedAwayPVGlobalDecayConstant t δ *
            (1 + |(x - a') / s'|)⁻¹) +
        (fixedAwayPVGlobalDecayConstant t δ *
            (1 + |(x - a) / s|)⁻¹) *
          (|s'|⁻¹ *
            (fixedAwayDerivativeCauchyConstant t δ *
              (1 + ((x - a') / s') ^ 2)⁻¹)) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv]
      apply add_le_add
      · apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left
            (norm_deriv_fixedAwayPVTransform_smooth_le_cauchyEnvelope
              hδ hδt.le (div_ne_zero (sub_ne_zero.mpr hxa) hs))
            (inv_nonneg.mpr (abs_nonneg s))
        · exact norm_fixedAwayPVTransform_smooth_le_globalDecay hδ hδt _
        · exact norm_nonneg _
        · exact mul_nonneg (inv_nonneg.mpr (abs_nonneg s))
            (mul_nonneg (fixedAwayDerivativeCauchyConstant_nonneg t δ)
              (inv_nonneg.mpr (by positivity)))
      · apply mul_le_mul
        · exact norm_fixedAwayPVTransform_smooth_le_globalDecay hδ hδt _
        · apply mul_le_mul_of_nonneg_left
            (norm_deriv_fixedAwayPVTransform_smooth_le_cauchyEnvelope
              hδ hδt.le (div_ne_zero (sub_ne_zero.mpr hxa') hs'))
            (inv_nonneg.mpr (abs_nonneg s'))
        · exact mul_nonneg (inv_nonneg.mpr (abs_nonneg s'))
            (norm_nonneg _)
        · exact mul_nonneg (fixedAwayPVGlobalDecayConstant_nonneg t δ)
            (inv_nonneg.mpr (by positivity))

def fixedAwayScaledCauchyEnvelope (s a x : ℝ) : ℝ :=
  |s|⁻¹ * (1 + ((x - a) / s) ^ 2)⁻¹

theorem integrable_fixedAwayScaledCauchyEnvelope
    {s a : ℝ} (hs : s ≠ 0) :
    Integrable (fixedAwayScaledCauchyEnvelope s a) := by
  have hdiv := integrable_inv_one_add_sq.comp_div hs
  have hshift := hdiv.comp_sub_right a
  have hmul := hshift.const_mul |s|⁻¹
  simpa only [fixedAwayScaledCauchyEnvelope, Function.comp_apply]
    using! hmul

theorem integrable_deriv_fixedAwayScaledHermitianProduct
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (hs : s ≠ 0) (hs' : s' ≠ 0) :
    Integrable
      (fun x : ℝ ↦ deriv
        (fixedAwayScaledHermitianProduct t δ s a s' a') x) := by
  let K : ℝ := fixedAwayDerivativeCauchyConstant t δ
  let G : ℝ := fixedAwayPVGlobalDecayConstant t δ
  let H : ℝ → ℝ := fun x ↦ K * G *
    (fixedAwayScaledCauchyEnvelope s a x +
      fixedAwayScaledCauchyEnvelope s' a' x)
  have hH : Integrable H := by
    exact ((integrable_fixedAwayScaledCauchyEnvelope hs).add
      (integrable_fixedAwayScaledCauchyEnvelope hs')).const_mul (K * G)
  apply hH.mono' (measurable_deriv _).aestronglyMeasurable
  filter_upwards [(volume : Measure ℝ).ae_ne a,
    (volume : Measure ℝ).ae_ne a'] with x hxa hxa'
  have hraw := norm_deriv_fixedAwayScaledHermitianProduct_le
    hδ hδt hs hs' hxa hxa'
  have hK : 0 ≤ K := fixedAwayDerivativeCauchyConstant_nonneg t δ
  have hG : 0 ≤ G := fixedAwayPVGlobalDecayConstant_nonneg t δ
  have hr1 : G * (1 + |(x - a) / s|)⁻¹ ≤ G := by
    apply mul_le_of_le_one_right hG
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (abs_nonneg _))
  have hr2 : G * (1 + |(x - a') / s'|)⁻¹ ≤ G := by
    apply mul_le_of_le_one_right hG
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right (abs_nonneg _))
  calc
    ‖deriv (fixedAwayScaledHermitianProduct t δ s a s' a') x‖ ≤
        |s|⁻¹ * (K * (1 + ((x - a) / s) ^ 2)⁻¹) *
            (G * (1 + |(x - a') / s'|)⁻¹) +
          (G * (1 + |(x - a) / s|)⁻¹) *
            (|s'|⁻¹ * (K * (1 + ((x - a') / s') ^ 2)⁻¹)) := hraw
    _ ≤ |s|⁻¹ * (K * (1 + ((x - a) / s) ^ 2)⁻¹) * G +
          G * (|s'|⁻¹ * (K * (1 + ((x - a') / s') ^ 2)⁻¹)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hr2 (by positivity)
      · exact mul_le_mul_of_nonneg_right hr1 (by positivity)
    _ = H x := by
      dsimp only [H, fixedAwayScaledCauchyEnvelope]
      ring

/-- Total carrier-point cost for the chosen convention `Rχ(0)=0`.
For distinct carriers each point contributes twice the one-sided magnitude;
when the carriers coincide, the product has one-sided value `π²` on both
sides and the isolated zero contributes `2π²`. -/
def fixedAwayHermitianCarrierJumpCost
    (t δ s a s' a' : ℝ) : ℝ :=
  if a = a' then 2 * Real.pi ^ 2 else
    2 * Real.pi *
      (‖fixedAwayScaledPV t δ s' a' a‖ +
        ‖fixedAwayScaledPV t δ s a a'‖)

theorem fixedAwayHermitianCarrierJumpCost_eq_diagonal
    (t δ s s' a : ℝ) :
    fixedAwayHermitianCarrierJumpCost t δ s a s' a =
      2 * Real.pi ^ 2 := by
  simp [fixedAwayHermitianCarrierJumpCost]

theorem fixedAwayHermitianCarrierJumpCost_le_of_ne
    {t δ s a s' a' : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (haa' : a ≠ a') :
    fixedAwayHermitianCarrierJumpCost t δ s a s' a' ≤
      2 * Real.pi * fixedAwayPVGlobalDecayConstant t δ *
        ((1 + |(a - a') / s'|)⁻¹ +
          (1 + |(a' - a) / s|)⁻¹) := by
  rw [fixedAwayHermitianCarrierJumpCost, if_neg haa']
  have hfirst := norm_fixedAwayPVTransform_smooth_le_globalDecay
    hδ hδt ((a - a') / s')
  have hsecond := norm_fixedAwayPVTransform_smooth_le_globalDecay
    hδ hδt ((a' - a) / s)
  unfold fixedAwayScaledPV
  calc
    2 * Real.pi *
        (‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
            ((a - a') / s')‖ +
          ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
            ((a' - a) / s)‖) ≤
      2 * Real.pi *
        (fixedAwayPVGlobalDecayConstant t δ *
            (1 + |(a - a') / s'|)⁻¹ +
          fixedAwayPVGlobalDecayConstant t δ *
            (1 + |(a' - a) / s|)⁻¹) := by
        gcongr
    _ = 2 * Real.pi * fixedAwayPVGlobalDecayConstant t δ *
        ((1 + |(a - a') / s'|)⁻¹ +
          (1 + |(a' - a) / s|)⁻¹) := by ring

end

end Erdos1002
