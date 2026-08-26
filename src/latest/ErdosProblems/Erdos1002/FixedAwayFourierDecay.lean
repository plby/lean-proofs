import ErdosProblems.Erdos1002.FixedAwayPVDerivative
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fourier decay of the fixed-away principal-value derivative

This file identifies the derivative of the paired principal-value transform
with the ordinary Fourier transform of its compact correction.  The proof
keeps the complex conjugate on the negative half-line explicit.  Smoothness
and compact support then give a rigorous arbitrary-order polynomial Fourier
bound by the library's iterated-derivative identity.
-/

open Filter MeasureTheory Set
open scoped ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

def realCutoffComplex (κ : ℝ → ℝ) (x : ℝ) : ℂ := (κ x : ℂ)

theorem fourier_realCutoffComplex_eq_two_cosine
    (κ : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hκcont : Continuous κ) (hκeven : Function.Even κ)
    (hκzero : ∀ x, C ≤ |x| → κ x = 0) (y : ℝ) :
    FourierTransform.fourier (realCutoffComplex κ) y =
      ((2 * (∫ v in (0 : ℝ)..C,
        κ v * Real.cos ((2 * Real.pi * y) * v)) : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun v ↦
    Complex.exp (((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I) *
      (κ v : ℂ)
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hsupport : ∀ v ∉ Ioc (-C) C, g v = 0 := by
    intro v hv
    have hout : C ≤ |v| := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with hv | hv
      · have hvnonpos : v ≤ 0 := hv.trans (neg_nonpos.mpr hC)
        rw [abs_of_nonpos hvnonpos]
        linarith
      · have hvpos : 0 < v := lt_of_le_of_lt hC hv
        rw [abs_of_pos hvpos]
        exact hv.le
    simp [g, hκzero v hout]
  have hfull : (∫ v : ℝ, g v) = ∫ v in -C..C, g v := by
    calc
      (∫ v : ℝ, g v) =
          ∫ v : ℝ, (Ioc (-C) C).indicator g v := by
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ∈ Ioc (-C) C
        · simp [hv]
        · simp [hv, hsupport v hv]
      _ = ∫ v in Ioc (-C) C, g v :=
        integral_indicator measurableSet_Ioc
      _ = ∫ v in -C..C, g v :=
        (intervalIntegral.integral_of_le (by linarith : -C ≤ C)).symm
  let A : ℂ := ∫ v in (0 : ℝ)..C, g v
  have hright : IntervalIntegrable g volume 0 C :=
    hgcont.intervalIntegrable 0 C
  have hleft : IntervalIntegrable g volume (-C) 0 :=
    hgcont.intervalIntegrable (-C) 0
  have hgneg (v : ℝ) : g (-v) = conj (g v) := by
    dsimp [g]
    rw [hκeven v]
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
      Complex.conj_I]
    congr 2
    push_cast
    ring
  have hleftEq : (∫ v in -C..(0 : ℝ), g v) = conj A := by
    calc
      (∫ v in -C..(0 : ℝ), g v) =
          ∫ v in (0 : ℝ)..C, g (-v) := by
        simpa only [neg_zero] using! (intervalIntegral.integral_comp_neg
          (a := (0 : ℝ)) (b := C) g).symm
      _ = ∫ v in (0 : ℝ)..C, conj (g v) := by
        apply intervalIntegral.integral_congr
        intro v _hv
        exact hgneg v
      _ = conj A := by
        have hstar := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
          |>.intervalIntegral_comp_comm hright
        simpa only [A, starL'_apply] using! hstar
  have hsymm : (∫ v in -C..C, g v) = conj A + A := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
      hleftEq]
  have hre : A.re = ∫ v in (0 : ℝ)..C,
      κ v * Real.cos ((2 * Real.pi * y) * v) := by
    have hrecomm := Complex.reCLM.intervalIntegral_comp_comm hright
    calc
      A.re = ∫ v in (0 : ℝ)..C, (g v).re := by
        simpa only [A, Complex.reCLM_apply] using! hrecomm.symm
      _ = ∫ v in (0 : ℝ)..C,
          κ v * Real.cos ((2 * Real.pi * y) * v) := by
        apply intervalIntegral.integral_congr
        intro v _hv
        dsimp [g]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
        rw [show -2 * Real.pi * v * y = -(2 * Real.pi * y * v) by ring,
          Real.cos_neg]
        ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ v : ℝ, g v) = _
  rw [hfull, hsymm]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.ofReal_re]
    rw [hre]
    ring
  · simp

theorem hasDerivAt_fixedAwayPVTransform_eq_fourier
    (κ : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hκcont : Continuous κ) (hκeven : Function.Even κ)
    (hκzero : ∀ x, C ≤ |x| → κ x = 0) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fixedAwayPVTransform κ C)
      ((2 * Real.pi * Complex.I) *
        FourierTransform.fourier (realCutoffComplex κ) y) y := by
  have hderiv := hasDerivAt_fixedAwayPVTransform_of_ne κ C hκcont hy
  rw [fourier_realCutoffComplex_eq_two_cosine κ hC hκcont hκeven hκzero y]
  have hint : (∫ v in (0 : ℝ)..C,
      2 * Real.pi * κ v * Real.cos ((2 * Real.pi * y) * v)) =
      2 * Real.pi * (∫ v in (0 : ℝ)..C,
        κ v * Real.cos ((2 * Real.pi * y) * v)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _hv
    ring
  rw [hint] at hderiv
  convert! hderiv using 1
  push_cast
  ring

theorem realCutoffComplex_contDiff
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) :
    ContDiff ℝ (⊤ : ℕ∞) (realCutoffComplex κ) := by
  exact Complex.ofRealCLM.contDiff.comp hκ

theorem realCutoffComplex_hasCompactSupport
    (κ : ℝ → ℝ) {C : ℝ} (hκzero : ∀ x, C ≤ |x| → κ x = 0) :
    HasCompactSupport (realCutoffComplex κ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-C) C) isCompact_Icc ?_
  intro x hx
  have hout : ¬ C ≤ |x| := by
    intro hCx
    apply hx
    simp [realCutoffComplex, hκzero x hCx]
  have habs := abs_lt.mp (lt_of_not_ge hout)
  exact ⟨habs.1.le, habs.2.le⟩

private theorem realCutoffComplex_iteratedDeriv_hasCompactSupport
    (κ : ℝ → ℝ) {C : ℝ} (hκzero : ∀ x, C ≤ |x| → κ x = 0)
    (n : ℕ) :
    HasCompactSupport ((deriv^[n]) (realCutoffComplex κ)) := by
  induction n with
  | zero => simpa using! realCutoffComplex_hasCompactSupport κ hκzero
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

theorem realCutoffComplex_iteratedDeriv_integrable
    (κ : ℝ → ℝ) {C : ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκzero : ∀ x, C ≤ |x| → κ x = 0) (n : ℕ) :
    Integrable (iteratedDeriv n (realCutoffComplex κ)) volume := by
  rw [iteratedDeriv_eq_iterate]
  exact Continuous.integrable_of_hasCompactSupport (μ := volume)
    ((realCutoffComplex_contDiff κ hκ).iterate_deriv n).continuous
    (realCutoffComplex_iteratedDeriv_hasCompactSupport κ hκzero n)

def fixedAwayCorrectionDerivL1 (κ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, ‖iteratedDeriv n (realCutoffComplex κ) x‖

theorem fixedAwayCorrection_fourier_polynomial
    (κ : ℝ → ℝ) {C : ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκzero : ∀ x, C ≤ |x| → κ x = 0) (n : ℕ) (y : ℝ) :
    (2 * Real.pi * |y|) ^ n *
        ‖FourierTransform.fourier (realCutoffComplex κ) y‖ ≤
      fixedAwayCorrectionDerivL1 κ n := by
  have hfour := Real.fourier_iteratedDeriv
    (f := realCutoffComplex κ) (N := (⊤ : ℕ∞)) (n := n)
    (realCutoffComplex_contDiff κ hκ)
    (fun m _hm => realCutoffComplex_iteratedDeriv_integrable κ hκ hκzero m)
    (by simp)
  have heq := congrFun hfour y
  have hnorm : ‖FourierTransform.fourier
      (iteratedDeriv n (realCutoffComplex κ)) y‖ ≤
      ∫ v : ℝ, ‖iteratedDeriv n (realCutoffComplex κ) v‖ := by
    simpa only [Real.fourier_eq] using!
      (VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ ℝ)
        (iteratedDeriv n (realCutoffComplex κ)) y)
  rw [heq] at hnorm
  unfold fixedAwayCorrectionDerivL1
  convert! hnorm using 1
  rw [norm_smul]
  simp only [norm_pow, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg]
  norm_num

theorem fixedAwaySmoothCorrection_fourier_polynomial
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (n : ℕ) (y : ℝ) :
    (2 * Real.pi * |y|) ^ n *
        ‖FourierTransform.fourier
          (realCutoffComplex (fixedAwaySmoothCorrection t δ)) y‖ ≤
      fixedAwayCorrectionDerivL1 (fixedAwaySmoothCorrection t δ) n := by
  apply fixedAwayCorrection_fourier_polynomial
    (κ := fixedAwaySmoothCorrection t δ)
    (C := t) (fixedAwaySmoothCorrection_contDiff t δ)
  intro x hx
  exact fixedAwaySmoothCorrection_eq_zero_of_le_abs hδ hδt hx

theorem hasDerivAt_fixedAwayPVTransform_smooth_eq_fourier
    {t δ y : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (hy : y ≠ 0) :
    HasDerivAt
      (fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t)
      ((2 * Real.pi * Complex.I) *
        FourierTransform.fourier
          (realCutoffComplex (fixedAwaySmoothCorrection t δ)) y) y := by
  apply hasDerivAt_fixedAwayPVTransform_eq_fourier
    (κ := fixedAwaySmoothCorrection t δ) (C := t)
  · exact hδ.le.trans hδt
  · exact (fixedAwaySmoothCorrection_contDiff
      (m := (⊤ : ℕ∞)) t δ).continuous
  · exact fixedAwaySmoothCorrection_even t δ
  · intro x hx
    exact fixedAwaySmoothCorrection_eq_zero_of_le_abs hδ hδt hx
  · exact hy

end

end Erdos1002
