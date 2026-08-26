import ErdosProblems.Erdos520.HarperEulerProduct
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators FourierTransform ComplexConjugate

namespace Erdos
namespace Problem520

/-!
# Harman--Parseval for the finite Rademacher Euler product

The random Euler product in #520 is a finite Dirichlet polynomial.  This file
proves the Cauchy-kernel Fourier identity needed to identify its full vertical
square integral with the existing inverse-square partial-sum energy.
-/

private noncomputable def cauchyFourierSeed (u : ℝ) : ℂ :=
  Complex.exp ((-(|u| / 2) : ℝ) : ℂ)

private theorem continuous_cauchyFourierSeed :
    Continuous cauchyFourierSeed := by
  unfold cauchyFourierSeed
  fun_prop

private theorem integrable_cauchyFourierSeed :
    Integrable cauchyFourierSeed := by
  have hleft : IntegrableOn cauchyFourierSeed (Iic (0 : ℝ)) := by
    have h := integrableOn_exp_mul_complex_Iic
      (a := (1 / 2 : ℝ)) (by norm_num) 0
    apply h.congr_fun
    intro u hu
    unfold cauchyFourierSeed
    rw [abs_of_nonpos hu]
    congr 1
    push_cast
    ring_nf
    exact measurableSet_Iic
  have hright : IntegrableOn cauchyFourierSeed (Ioi (0 : ℝ)) := by
    have h := integrableOn_exp_mul_complex_Ioi
      (a := (-1 / 2 : ℝ)) (by norm_num) 0
    apply h.congr_fun
    intro u hu
    unfold cauchyFourierSeed
    rw [abs_of_pos hu]
    congr 1
    push_cast
    ring_nf
    exact measurableSet_Ioi
  rw [← integrableOn_univ]
  simpa only [Iic_union_Ioi] using! hleft.union hright

private theorem cauchyComplexAlgebra (b : ℝ) :
    (((1 / 2 : ℝ) : ℂ) - (b : ℂ) * Complex.I)⁻¹ -
      (((-1 / 2 : ℝ) : ℂ) - (b : ℂ) * Complex.I)⁻¹ =
        ((((1 / 4 : ℝ) + b ^ 2)⁻¹ : ℝ) : ℂ) := by
  apply Complex.ext <;>
    norm_num [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
      Complex.div_re, Complex.div_im, ← Complex.ofReal_pow] <;>
    field_simp <;>
    ring_nf

private theorem fourier_cauchyFourierSeed (w : ℝ) :
    FourierTransform.fourier cauchyFourierSeed w =
      (1 : ℂ) / (((1 / 4 : ℝ) + (2 * Real.pi * w) ^ 2 : ℝ) : ℂ) := by
  let leftRate : ℂ := (1 / 2 : ℝ) - (2 * Real.pi * w : ℝ) * Complex.I
  let rightRate : ℂ := (-1 / 2 : ℝ) - (2 * Real.pi * w : ℝ) * Complex.I
  let integrand : ℝ → ℂ := fun u ↦
    Complex.exp ((-2 * Real.pi * u * w : ℝ) * Complex.I) •
      cauchyFourierSeed u
  have hInt : Integrable integrand := by
    have hexp : Continuous (fun u : ℝ ↦
        Complex.exp ((-2 * Real.pi * u * w : ℝ) * Complex.I)) := by
      apply Complex.continuous_exp.comp
      fun_prop
    have hmeas : AEStronglyMeasurable integrand := by
      exact (hexp.smul continuous_cauchyFourierSeed).aestronglyMeasurable
    apply (integrable_norm_iff hmeas).mp
    convert! integrable_cauchyFourierSeed.norm using 1
    funext u
    unfold integrand
    rw [norm_smul, Complex.norm_exp]
    simp
  have hleft :
      (∫ u in Iic (0 : ℝ), integrand u) =
        ∫ u in Iic (0 : ℝ), Complex.exp (leftRate * u) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro u hu
    unfold integrand cauchyFourierSeed leftRate
    rw [abs_of_nonpos hu]
    simp only [smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hright :
      (∫ u in Ioi (0 : ℝ), integrand u) =
        ∫ u in Ioi (0 : ℝ), Complex.exp (rightRate * u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    unfold integrand cauchyFourierSeed rightRate
    rw [abs_of_pos hu]
    simp only [smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hleftRate : 0 < leftRate.re := by
    norm_num [leftRate]
  have hrightRate : rightRate.re < 0 := by
    norm_num [rightRate]
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ u : ℝ, integrand u) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi
      hInt.integrableOn hInt.integrableOn,
    hleft, hright, integral_exp_mul_complex_Iic hleftRate,
    integral_exp_mul_complex_Ioi hrightRate]
  unfold leftRate rightRate
  push_cast
  simpa [Complex.exp_zero, div_eq_mul_inv, mul_assoc, mul_comm,
    mul_left_comm, pow_two] using!
    cauchyComplexAlgebra (2 * Real.pi * w)

private theorem integrable_fourier_cauchyFourierSeed :
    Integrable (FourierTransform.fourier cauchyFourierSeed) := by
  have hbase : Integrable (fun w : ℝ ↦ (1 + w ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hscale : (4 * Real.pi : ℝ) ≠ 0 := by positivity
  have hscaled := hbase.comp_mul_left' hscale
  have hreal : Integrable (fun w : ℝ ↦
      4 * (1 + (4 * Real.pi * w) ^ 2)⁻¹) :=
    hscaled.const_mul 4
  have hcomplex : Integrable (fun w : ℝ ↦
      ((4 * (1 + (4 * Real.pi * w) ^ 2)⁻¹ : ℝ) : ℂ)) :=
    hreal.ofReal
  apply hcomplex.congr
  exact ae_of_all volume fun w ↦ by
    rw [fourier_cauchyFourierSeed]
    norm_cast
    field_simp
    ring_nf

/-- The complex form of the Cauchy-kernel Fourier identity, with the
normalization used by the Euler product. -/
theorem integral_complexExp_mul_div_cauchyKernel (u : ℝ) :
    (∫ t : ℝ, Complex.exp ((t * u : ℝ) * Complex.I) /
        (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)) =
      (2 * Real.pi : ℝ) * Complex.exp ((-(|u| / 2) : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun t ↦
    Complex.exp ((t * u : ℝ) * Complex.I) /
      (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)
  have hinv := congrFun
    (continuous_cauchyFourierSeed.fourierInv_fourier_eq
      integrable_cauchyFourierSeed integrable_fourier_cauchyFourierSeed) u
  rw [Real.fourierInv_eq'] at hinv
  simp_rw [fourier_cauchyFourierSeed] at hinv
  have hscaled :
      (∫ w : ℝ, g ((2 * Real.pi) * w)) =
        |((2 * Real.pi : ℝ)⁻¹)| • ∫ t : ℝ, g t :=
    Measure.integral_comp_mul_left g (2 * Real.pi)
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmatch :
      (∫ w : ℝ,
          Complex.exp ((↑(2 * Real.pi * inner ℝ w u) : ℂ) * Complex.I) •
            ((1 : ℂ) /
              (((1 / 4 : ℝ) + (2 * Real.pi * w) ^ 2 : ℝ) : ℂ))) =
        ∫ w : ℝ, g ((2 * Real.pi) * w) := by
    apply integral_congr_ae
    exact ae_of_all volume fun w ↦ by
      change
        Complex.exp ((↑(2 * Real.pi * inner ℝ w u) : ℂ) * Complex.I) •
            ((1 : ℂ) /
              (((1 / 4 : ℝ) + (2 * Real.pi * w) ^ 2 : ℝ) : ℂ)) =
          g ((2 * Real.pi) * w)
      unfold g
      rw [show inner ℝ w u = w * u by
        change u * w = w * u
        ring]
      simp only [smul_eq_mul, one_div, one_mul]
      congr 2
      · congr 2
        push_cast
        ring_nf
  rw [hmatch, hscaled] at hinv
  unfold cauchyFourierSeed at hinv
  rw [abs_inv, abs_of_pos hpi] at hinv
  have hmul := congrArg (fun z : ℂ ↦ (2 * Real.pi : ℝ) • z) hinv
  have hne : (2 * Real.pi : ℝ) ≠ 0 := hpi.ne'
  have hcoef :
      ((2 * Real.pi : ℝ) : ℂ) * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) = 1 := by
    norm_cast
    exact mul_inv_cancel₀ hne
  simp only [Complex.real_smul, ← mul_assoc] at hmul
  rw [hcoef, one_mul] at hmul
  simpa only [g, Complex.real_smul] using! hmul

private theorem integrable_complexExp_mul_div_cauchyKernel (u : ℝ) :
    Integrable (fun t : ℝ ↦
      Complex.exp ((t * u : ℝ) * Complex.I) /
        (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)) := by
  have hbase : Integrable (fun t : ℝ ↦ (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have hscaled := hbase.comp_mul_left' (show (2 : ℝ) ≠ 0 by norm_num)
  have hreal : Integrable (fun t : ℝ ↦
      4 * (1 + (2 * t) ^ 2)⁻¹) := hscaled.const_mul 4
  have hcomplex : Integrable (fun t : ℝ ↦
      ((4 * (1 + (2 * t) ^ 2)⁻¹ : ℝ) : ℂ)) := hreal.ofReal
  have hden : Integrable (fun t : ℝ ↦
      (1 : ℂ) / (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)) := by
    apply hcomplex.congr
    exact ae_of_all volume fun t ↦ by
      norm_cast
      field_simp
      ring_nf
  let e : ℝ → ℂ := fun t ↦ Complex.exp ((t * u : ℝ) * Complex.I)
  have he : Continuous e := by
    unfold e
    fun_prop
  have hprod := hden.bdd_mul
    (f := e) (c := 1) he.aestronglyMeasurable
    (ae_of_all volume fun t ↦ by
      unfold e
      rw [Complex.norm_exp]
      norm_num)
  simpa [e, div_eq_mul_inv] using! hprod

/-- The real Cauchy-kernel identity used term-by-term in the finite
Harman--Parseval expansion. -/
theorem integral_cos_mul_div_cauchyKernel (u : ℝ) :
    (∫ t : ℝ, Real.cos (t * u) / ((1 / 4 : ℝ) + t ^ 2)) =
      2 * Real.pi * Real.exp (-|u| / 2) := by
  have hInt := integrable_complexExp_mul_div_cauchyKernel u
  calc
    (∫ t : ℝ, Real.cos (t * u) / ((1 / 4 : ℝ) + t ^ 2)) =
        Complex.re (∫ t : ℝ, Complex.exp ((t * u : ℝ) * Complex.I) /
          (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)) := by
      have hre := integral_re hInt
      change
        (∫ t : ℝ, Complex.re (Complex.exp ((t * u : ℝ) * Complex.I) /
          (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ))) =
            Complex.re (∫ t : ℝ, Complex.exp ((t * u : ℝ) * Complex.I) /
              (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)) at hre
      rw [← hre]
      apply integral_congr_ae
      exact ae_of_all volume fun t ↦ by
        change Real.cos (t * u) / ((1 / 4 : ℝ) + t ^ 2) =
          (Complex.exp ((t * u : ℝ) * Complex.I) /
            (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)).re
        rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re,
          Complex.ofReal_im, Complex.exp_ofReal_mul_I_re]
        have hden : (1 / 4 : ℝ) + t ^ 2 ≠ 0 := by positivity
        field_simp [hden]
        ring
    _ = Complex.re ((2 * Real.pi : ℝ) *
          Complex.exp ((-(|u| / 2) : ℝ) : ℂ)) :=
      congrArg Complex.re (integral_complexExp_mul_div_cauchyKernel u)
    _ = 2 * Real.pi * Real.exp (-|u| / 2) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_re, zero_mul, sub_zero]
      congr 1
      ring_nf

private theorem integrable_cos_mul_div_cauchyKernel (u : ℝ) :
    Integrable (fun t : ℝ ↦
      Real.cos (t * u) / ((1 / 4 : ℝ) + t ^ 2)) := by
  have h := (integrable_complexExp_mul_div_cauchyKernel u).re
  apply h.congr
  exact ae_of_all volume fun t ↦ by
    change (Complex.exp ((t * u : ℝ) * Complex.I) /
        (((1 / 4 : ℝ) + t ^ 2 : ℝ) : ℂ)).re =
      Real.cos (t * u) / ((1 / 4 : ℝ) + t ^ 2)
    rw [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re]
    have hden : (1 / 4 : ℝ) + t ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    ring

/-- The exponential kernel supplied by the Cauchy transform exactly cancels
the two critical-line square roots and leaves the reciprocal of the larger
Dirichlet index. -/
theorem exp_neg_abs_log_sub_div_sqrt_mul
    {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    Real.exp (-|Real.log d - Real.log e| / 2) /
        (Real.sqrt d * Real.sqrt e) =
      1 / max d e := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  by_cases hde : d ≤ e
  · have hlog : Real.log d ≤ Real.log e :=
      Real.strictMonoOn_log.monotoneOn hd he hde
    rw [max_eq_right hde, abs_of_nonpos (sub_nonpos.mpr hlog)]
    have hexp :
        Real.exp (-(Real.log e - Real.log d) / 2) =
          Real.sqrt d / Real.sqrt e := by
      rw [show -(Real.log e - Real.log d) / 2 =
          Real.log (Real.sqrt d) - Real.log (Real.sqrt e) by
        rw [Real.log_sqrt hd.le, Real.log_sqrt he.le]
        ring]
      rw [Real.exp_sub, Real.exp_log hsd, Real.exp_log hse]
    rw [show - -(Real.log d - Real.log e) / 2 =
        -(Real.log e - Real.log d) / 2 by ring, hexp]
    field_simp [hsd.ne', hse.ne']
    rw [Real.sq_sqrt he.le]
  · have hed : e ≤ d := le_of_not_ge hde
    have hlog : Real.log e ≤ Real.log d :=
      Real.strictMonoOn_log.monotoneOn he hd hed
    rw [max_eq_left hed, abs_of_nonneg (sub_nonneg.mpr hlog)]
    have hexp :
        Real.exp (-(Real.log d - Real.log e) / 2) =
          Real.sqrt e / Real.sqrt d := by
      rw [show -(Real.log d - Real.log e) / 2 =
          Real.log (Real.sqrt e) - Real.log (Real.sqrt d) by
        rw [Real.log_sqrt he.le, Real.log_sqrt hd.le]
        ring]
      rw [Real.exp_sub, Real.exp_log hse, Real.exp_log hsd]
    rw [hexp]
    field_simp [hsd.ne', hse.ne']
    rw [Real.sq_sqrt hd.le]

/-! ## A finite Harman--Parseval identity -/

/-- Harman--Parseval for an arbitrary finite real Dirichlet polynomial.
This form isolates all Fourier analysis from the squarefree-smooth
specialization below. -/
theorem integral_finiteDirichletCosineDensity
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a d : ι → ℝ) (hd : ∀ i ∈ s, 0 < d i) :
    (∫ t : ℝ,
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * a j / (Real.sqrt (d i) * Real.sqrt (d j))) *
            Real.cos (t * (Real.log (d i) - Real.log (d j)))) /
          ((1 / 4 : ℝ) + t ^ 2)) =
      2 * Real.pi *
        ∑ i ∈ s, ∑ j ∈ s, a i * a j / max (d i) (d j) := by
  let term : ι → ι → ℝ → ℝ := fun i j t ↦
    (a i * a j / (Real.sqrt (d i) * Real.sqrt (d j))) *
      (Real.cos (t * (Real.log (d i) - Real.log (d j))) /
        ((1 / 4 : ℝ) + t ^ 2))
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      Integrable (term i j) := by
    exact (integrable_cos_mul_div_cauchyKernel
      (Real.log (d i) - Real.log (d j))).const_mul _
  calc
    (∫ t : ℝ,
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * a j / (Real.sqrt (d i) * Real.sqrt (d j))) *
            Real.cos (t * (Real.log (d i) - Real.log (d j)))) /
          ((1 / 4 : ℝ) + t ^ 2)) =
        ∫ t : ℝ, ∑ i ∈ s, ∑ j ∈ s, term i j t := by
      congr 1
      funext t
      unfold term
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ t : ℝ, term i j t := by
      rw [integral_finset_sum s]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finset_sum s (hterm i hi)]
      · intro i hi
        exact integrable_finset_sum s (hterm i hi)
    _ = ∑ i ∈ s, ∑ j ∈ s,
        (a i * a j / (Real.sqrt (d i) * Real.sqrt (d j))) *
          (2 * Real.pi *
            Real.exp (-|Real.log (d i) - Real.log (d j)| / 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      unfold term
      rw [integral_const_mul, integral_cos_mul_div_cauchyKernel]
    _ = 2 * Real.pi *
        ∑ i ∈ s, ∑ j ∈ s, a i * a j / max (d i) (d j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hk := exp_neg_abs_log_sub_div_sqrt_mul (hd i hi) (hd j hj)
      calc
        a i * a j / (Real.sqrt (d i) * Real.sqrt (d j)) *
            (2 * Real.pi *
              Real.exp (-|Real.log (d i) - Real.log (d j)| / 2)) =
            2 * Real.pi * (a i * a j) *
              (Real.exp (-|Real.log (d i) - Real.log (d j)| / 2) /
                (Real.sqrt (d i) * Real.sqrt (d j))) := by ring
        _ = 2 * Real.pi * (a i * a j) *
              (1 / max (d i) (d j)) := by rw [hk]
        _ = 2 * Real.pi * (a i * a j / max (d i) (d j)) := by ring

/-- Integrability of the elementary tail kernel occurring after a finite
partial-sum square is expanded. -/
private theorem integrableOn_tailIndicator_div_sq
    {m : ℝ} (hm : 0 < m) (c : ℝ) :
    IntegrableOn (fun z : ℝ ↦ if m ≤ z then c / z ^ 2 else 0)
      (Ioi (0 : ℝ)) := by
  have hpow : IntegrableOn (fun z : ℝ ↦ c * z ^ (-2 : ℝ)) (Ioi m) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hm).const_mul c
  have hpowIci : IntegrableOn (fun z : ℝ ↦ c * z ^ (-2 : ℝ)) (Ici m) :=
    hpow.congr_set_ae Ioi_ae_eq_Ici.symm
  have hdivIci : IntegrableOn (fun z : ℝ ↦ c / z ^ 2) (Ici m) := by
    apply hpowIci.congr_fun
    · intro z hz
      have hzpos : 0 < z := hm.trans_le hz
      change c * z ^ (-2 : ℝ) = c / z ^ (2 : ℕ)
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hzpos.le, Real.rpow_two]
      ring
    · exact measurableSet_Ici
  rw [← integrable_indicator_iff measurableSet_Ioi]
  have hi := hdivIci.integrable_indicator measurableSet_Ici
  apply hi.congr
  exact ae_of_all volume fun z ↦ by
    by_cases hz : m ≤ z
    · have hzpos : 0 < z := hm.trans_le hz
      simp [Set.indicator, hz, hzpos]
    · simp [Set.indicator, hz]

/-- The inverse-square tail of two positive indices is the reciprocal of
their maximum. -/
private theorem integral_tailIndicator_div_sq
    {m : ℝ} (hm : 0 < m) (c : ℝ) :
    (∫ z in Ioi (0 : ℝ), if m ≤ z then c / z ^ 2 else 0) = c / m := by
  calc
    (∫ z in Ioi (0 : ℝ), if m ≤ z then c / z ^ 2 else 0) =
        ∫ z in Ici m, c / z ^ 2 := by
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      exact ae_of_all volume fun z ↦ by
        by_cases hz : m ≤ z
        · have hzpos : 0 < z := hm.trans_le hz
          simp [Set.indicator, hz, hzpos]
        · simp [Set.indicator, hz]
    _ = ∫ z in Ioi m, c / z ^ 2 := integral_Ici_eq_integral_Ioi
    _ = ∫ z in Ioi m, c * z ^ (-2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      have hzpos : 0 < z := hm.trans hz
      change c / z ^ (2 : ℕ) = c * z ^ (-2 : ℝ)
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
        Real.rpow_neg hzpos.le, Real.rpow_two]
      ring
    _ = c * ∫ z in Ioi m, z ^ (-2 : ℝ) := by
      rw [integral_const_mul]
    _ = c / m := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hm]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      simp [div_eq_mul_inv]

/-! ## The squarefree-smooth specialization -/

/-- At a nonnegative real cutoff, the smooth sum is the full squarefree
powerset sum with the cutoff written as an indicator. -/
theorem ΨReal_eq_sum_powerset_indicator
    (omega : Omega) (y : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ΨReal omega z y =
      ∑ S ∈ (y + 1).primesBelow.powerset,
        if (freshProduct S : ℝ) ≤ z then freshCharacter omega S else 0 := by
  rw [ΨReal, Ψ_eq_sum_squarefreeSmoothSets]
  unfold squarefreeSmoothSets
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Nat.le_floor_iff hz]

/-- Expanding the square of the real smooth sum gives a finite double tail
sum indexed by pairs of squarefree smooth integers. -/
theorem abs_ΨReal_sq_eq_sum_powerset_maxIndicator
    (omega : Omega) (y : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |ΨReal omega z y| ^ 2 =
      ∑ S ∈ (y + 1).primesBelow.powerset,
        ∑ T ∈ (y + 1).primesBelow.powerset,
          if max (freshProduct S : ℝ) (freshProduct T : ℝ) ≤ z then
            freshCharacter omega S * freshCharacter omega T else 0 := by
  rw [ΨReal_eq_sum_powerset_indicator omega y hz, sq_abs, pow_two,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hSz : (freshProduct S : ℝ) ≤ z <;>
    by_cases hTz : (freshProduct T : ℝ) ≤ z <;>
      simp [hSz, hTz, max_le_iff]

/-- Exact finite double-sum formula for the existing inverse-square smooth
energy. -/
theorem smoothEnergy_eq_sum_powerset_max
    (omega : Omega) (y : ℕ) :
    smoothEnergy omega y =
      ∑ S ∈ (y + 1).primesBelow.powerset,
        ∑ T ∈ (y + 1).primesBelow.powerset,
          freshCharacter omega S * freshCharacter omega T /
            max (freshProduct S : ℝ) (freshProduct T : ℝ) := by
  classical
  let P : Finset (Finset ℕ) := (y + 1).primesBelow.powerset
  have hprodPos (S : Finset ℕ) (hS : S ∈ P) :
      0 < (freshProduct S : ℝ) := by
    have hsub : S ⊆ (y + 1).primesBelow := by
      simpa only [P, Finset.mem_powerset] using! hS
    have hnat : 0 < freshProduct S :=
      freshProduct_pos_of_primes fun p hp ↦
        Nat.prime_of_mem_primesBelow (hsub hp)
    exact_mod_cast hnat
  have hmaxPos (S : Finset ℕ) (hS : S ∈ P)
      (T : Finset ℕ) (hT : T ∈ P) :
      0 < max (freshProduct S : ℝ) (freshProduct T : ℝ) :=
    lt_max_of_lt_left (hprodPos S hS)
  unfold smoothEnergy
  change
    (∫ z in Ioi (0 : ℝ), |ΨReal omega z y| ^ 2 / z ^ 2) = _
  calc
    (∫ z in Ioi (0 : ℝ), |ΨReal omega z y| ^ 2 / z ^ 2) =
        ∫ z in Ioi (0 : ℝ),
          ∑ S ∈ P, ∑ T ∈ P,
            if max (freshProduct S : ℝ) (freshProduct T : ℝ) ≤ z then
              freshCharacter omega S * freshCharacter omega T / z ^ 2
            else 0 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      change |ΨReal omega z y| ^ 2 / z ^ 2 =
        ∑ S ∈ P, ∑ T ∈ P,
          if max (freshProduct S : ℝ) (freshProduct T : ℝ) ≤ z then
            freshCharacter omega S * freshCharacter omega T / z ^ 2
          else 0
      rw [abs_ΨReal_sq_eq_sum_powerset_maxIndicator omega y hz.le]
      change
        (∑ S ∈ P, ∑ T ∈ P,
          if max (freshProduct S : ℝ) (freshProduct T : ℝ) ≤ z then
            freshCharacter omega S * freshCharacter omega T else 0) / z ^ 2 = _
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hmax : max (freshProduct S : ℝ) (freshProduct T : ℝ) ≤ z <;>
        simp [hmax]
    _ = ∑ S ∈ P, ∑ T ∈ P,
        ∫ z in Ioi (0 : ℝ),
          if max (freshProduct S : ℝ) (freshProduct T : ℝ) ≤ z then
            freshCharacter omega S * freshCharacter omega T / z ^ 2
          else 0 := by
      rw [integral_finset_sum P]
      · apply Finset.sum_congr rfl
        intro S hS
        rw [integral_finset_sum P]
        intro T hT
        exact integrableOn_tailIndicator_div_sq (hmaxPos S hS T hT) _
      · intro S hS
        exact integrable_finset_sum P fun T hT ↦
          integrableOn_tailIndicator_div_sq (hmaxPos S hS T hT) _
    _ = ∑ S ∈ P, ∑ T ∈ P,
        freshCharacter omega S * freshCharacter omega T /
          max (freshProduct S : ℝ) (freshProduct T : ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      exact integral_tailIndicator_div_sq (hmaxPos S hS T hT) _

/-- Logarithm of a squarefree prime product. -/
private theorem log_freshProduct
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) :
    Real.log (freshProduct S : ℝ) =
      ∑ p ∈ S, Real.log (p : ℝ) := by
  unfold freshProduct
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (hprime p hp).ne_zero

/-- Square root of a squarefree prime product. -/
private theorem sqrt_freshProduct
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) :
    Real.sqrt (freshProduct S : ℝ) =
      ∏ p ∈ S, Real.sqrt (p : ℝ) := by
  unfold freshProduct
  rw [Nat.cast_prod, Real.sqrt_prod]
  intro p hp
  positivity

private theorem prod_epsilon_div_sqrt
    (omega : Omega) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, ε omega p / Real.sqrt (p : ℝ)) =
      freshCharacter omega S / Real.sqrt (freshProduct S : ℝ) := by
  unfold freshCharacter
  rw [Finset.prod_div_distrib, sqrt_freshProduct hprime]

/-- A subset term in the product expansion is the corresponding critical
Dirichlet monomial. -/
private theorem prod_harperPrimeMonomial
    (omega : Omega) (t : ℝ) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S,
        (((ε omega p / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
          Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))) =
      ((freshCharacter omega S /
          Real.sqrt (freshProduct S : ℝ) : ℝ) : ℂ) *
        Complex.exp ((t * Real.log (freshProduct S : ℝ) : ℝ) *
          Complex.I) := by
  rw [Finset.prod_mul_distrib]
  have hcoeff := prod_epsilon_div_sqrt omega hprime
  have hcoeffC :
      (∏ p ∈ S, ((ε omega p / Real.sqrt (p : ℝ) : ℝ) : ℂ)) =
        ((freshCharacter omega S /
          Real.sqrt (freshProduct S : ℝ) : ℝ) : ℂ) := by
    norm_cast
  rw [hcoeffC, ← Complex.exp_sum]
  congr 2
  have hlog :
      (∑ p ∈ S, t * Real.log (p : ℝ)) =
        t * Real.log (freshProduct S : ℝ) := by
    rw [← Finset.mul_sum, ← log_freshProduct hprime]
  calc
    ∑ p ∈ S,
        (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) =
        (((∑ p ∈ S, t * Real.log (p : ℝ) : ℝ) : ℂ) *
          Complex.I) := by
      push_cast
      rw [Finset.sum_mul]
    _ = (((t * Real.log (freshProduct S : ℝ) : ℝ) : ℂ) *
          Complex.I) := by rw [hlog]

/-- The critical finite Dirichlet polynomial obtained by expanding the prime
Euler product. -/
noncomputable def harperDirichletPolynomial
    (y : ℕ) (omega : Omega) (t : ℝ) : ℂ :=
  ∑ S ∈ (y + 1).primesBelow.powerset,
    ((freshCharacter omega S /
        Real.sqrt (freshProduct S : ℝ) : ℝ) : ℂ) *
      Complex.exp ((t * Real.log (freshProduct S : ℝ) : ℝ) *
        Complex.I)

private noncomputable def harperComplexEulerFactor
    (omega : Omega) (p : ℕ) (t : ℝ) : ℂ :=
  1 + (((ε omega p / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
    Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))

/-- Expanding the finite prime Euler product gives exactly the squarefree
Dirichlet polynomial above. -/
theorem prod_harperComplexEulerFactor_eq_dirichletPolynomial
    (y : ℕ) (omega : Omega) (t : ℝ) :
    (∏ p ∈ (y + 1).primesBelow,
        harperComplexEulerFactor omega p t) =
      harperDirichletPolynomial y omega t := by
  classical
  unfold harperComplexEulerFactor harperDirichletPolynomial
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hS
  apply prod_harperPrimeMonomial
  intro p hp
  exact Nat.prime_of_mem_primesBelow ((Finset.mem_powerset.mp hS) hp)

private theorem normSq_harperComplexEulerFactor
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    Complex.normSq (harperComplexEulerFactor omega p t) =
      harperEulerFactor omega p t := by
  unfold harperComplexEulerFactor harperEulerFactor
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, sub_zero, zero_add, mul_zero, add_zero]
  ring

/-- The real Euler-product density is the squared norm of its complex
Dirichlet-polynomial expansion. -/
theorem harperEulerDensity_eq_normSq_dirichletPolynomial
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperEulerDensity y omega t =
      Complex.normSq (harperDirichletPolynomial y omega t) := by
  rw [← prod_harperComplexEulerFactor_eq_dirichletPolynomial]
  unfold harperEulerDensity
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  symm
  exact normSq_harperComplexEulerFactor omega
    (Nat.Prime.pos (Nat.prime_of_mem_primesBelow hp)) t

private theorem normSq_sum_real_mul_exp
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    Complex.normSq
        (∑ i ∈ s, ((a i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * Real.cos (b i - b j) := by
  classical
  have hre :
      (∑ i ∈ s, ((a i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)).re =
        ∑ i ∈ s, a i * Real.cos (b i) := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have him :
      (∑ i ∈ s, ((a i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)).im =
        ∑ i ∈ s, a i * Real.sin (b i) := by
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  rw [Complex.normSq_apply, hre, him]
  calc
    (∑ i ∈ s, a i * Real.cos (b i)) *
          (∑ j ∈ s, a j * Real.cos (b j)) +
        (∑ i ∈ s, a i * Real.sin (b i)) *
          (∑ j ∈ s, a j * Real.sin (b j)) =
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * Real.cos (b i)) * (a j * Real.cos (b j))) +
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * Real.sin (b i)) * (a j * Real.sin (b j))) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s,
          ((a i * Real.cos (b i)) * (a j * Real.cos (b j)) +
            (a i * Real.sin (b i)) * (a j * Real.sin (b j))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s,
          a i * a j * Real.cos (b i - b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.cos_sub]
      ring

/-- Pointwise squarefree cosine expansion of the Euler-product density. -/
theorem harperEulerDensity_eq_sum_powerset_cosine
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperEulerDensity y omega t =
      ∑ S ∈ (y + 1).primesBelow.powerset,
        ∑ T ∈ (y + 1).primesBelow.powerset,
          (freshCharacter omega S * freshCharacter omega T /
              (Real.sqrt (freshProduct S : ℝ) *
                Real.sqrt (freshProduct T : ℝ))) *
            Real.cos
              (t * (Real.log (freshProduct S : ℝ) -
                Real.log (freshProduct T : ℝ))) := by
  rw [harperEulerDensity_eq_normSq_dirichletPolynomial]
  unfold harperDirichletPolynomial
  rw [normSq_sum_real_mul_exp]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  · ring
  · congr 1
    ring

/-- Exact Harman--Parseval identity for the critical finite Euler product:
its full Cauchy-weighted vertical mass is precisely the inverse-square smooth
partial-sum energy already used in the #520 reduction. -/
theorem integral_harperEulerDensity_div_cauchyKernel
    (y : ℕ) (omega : Omega) :
    (∫ t : ℝ, harperEulerDensity y omega t /
        ((1 / 4 : ℝ) + t ^ 2)) =
      2 * Real.pi * smoothEnergy omega y := by
  classical
  let P : Finset (Finset ℕ) := (y + 1).primesBelow.powerset
  have hprodPos (S : Finset ℕ) (hS : S ∈ P) :
      0 < (freshProduct S : ℝ) := by
    have hsub : S ⊆ (y + 1).primesBelow := by
      simpa only [P, Finset.mem_powerset] using! hS
    have hnat : 0 < freshProduct S :=
      freshProduct_pos_of_primes fun p hp ↦
        Nat.prime_of_mem_primesBelow (hsub hp)
    exact_mod_cast hnat
  have h := integral_finiteDirichletCosineDensity P
    (fun S ↦ freshCharacter omega S)
    (fun S ↦ (freshProduct S : ℝ)) hprodPos
  simpa only [P, harperEulerDensity_eq_sum_powerset_cosine,
    smoothEnergy_eq_sum_powerset_max] using! h

/-- Continuity in the vertical parameter; in particular the density is
integrable on every bounded interval. -/
theorem continuous_harperEulerDensity_vertical
    (y : ℕ) (omega : Omega) :
    Continuous (fun t : ℝ ↦ harperEulerDensity y omega t) := by
  unfold harperEulerDensity harperEulerFactor
  fun_prop

/-- Global integrability after multiplication by the Cauchy kernel. -/
theorem integrable_harperEulerDensity_div_cauchyKernel
    (y : ℕ) (omega : Omega) :
    Integrable (fun t : ℝ ↦
      harperEulerDensity y omega t / ((1 / 4 : ℝ) + t ^ 2)) := by
  classical
  let P : Finset (Finset ℕ) := (y + 1).primesBelow.powerset
  let term : Finset ℕ → Finset ℕ → ℝ → ℝ := fun S T t ↦
    (freshCharacter omega S * freshCharacter omega T /
        (Real.sqrt (freshProduct S : ℝ) *
          Real.sqrt (freshProduct T : ℝ))) *
      (Real.cos (t * (Real.log (freshProduct S : ℝ) -
        Real.log (freshProduct T : ℝ))) /
          ((1 / 4 : ℝ) + t ^ 2))
  have hterm (S T : Finset ℕ) : Integrable (term S T) := by
    exact (integrable_cos_mul_div_cauchyKernel
      (Real.log (freshProduct S : ℝ) -
        Real.log (freshProduct T : ℝ))).const_mul _
  have hsum : Integrable (fun t : ℝ ↦
      ∑ S ∈ P, ∑ T ∈ P, term S T t) :=
    integrable_finset_sum P fun S hS ↦
      integrable_finset_sum P fun T hT ↦ hterm S T
  apply hsum.congr
  exact ae_of_all volume fun t ↦ by
    change (∑ S ∈ P, ∑ T ∈ P, term S T t) =
      harperEulerDensity y omega t / ((1 / 4 : ℝ) + t ^ 2)
    rw [harperEulerDensity_eq_sum_powerset_cosine]
    change
      (∑ S ∈ P, ∑ T ∈ P, term S T t) =
        (∑ S ∈ P, ∑ T ∈ P,
          (freshCharacter omega S * freshCharacter omega T /
              (Real.sqrt (freshProduct S : ℝ) *
                Real.sqrt (freshProduct T : ℝ))) *
            Real.cos (t * (Real.log (freshProduct S : ℝ) -
              Real.log (freshProduct T : ℝ)))) /
          ((1 / 4 : ℝ) + t ^ 2)
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    unfold term
    ring

end Problem520
end Erdos
