/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierLaplace
import ErdosProblems.Erdos4b.GeneralFourierLocalFactor

/-!
# Fourier inversion for the exponential Selberg profiles

The `2π` scaling is explicit. A Schwartz extension `H(t) = exp(t) F(t)`
produces a Schwartz frequency coefficient whose Laplace profile is `F`.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff

theorem laplaceFourierProfile_eq_exp_mul_fourier (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    laplaceFourierProfile f t =
      Complex.exp (-(t : ℂ)) * (𝓕 (f : ℝ → ℂ)) (t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  unfold laplaceFourierProfile
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hphase : -fourierLaplaceParameter ξ * (t : ℂ) =
      -(t : ℂ) + ((-2 * Real.pi * ξ * (t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
    have hr : -2 * Real.pi * ξ * (t / (2 * Real.pi)) = -ξ * t := by
      field_simp
    rw [hr]
    unfold fourierLaplaceParameter
    push_cast
    ring
  rw [hphase, Complex.exp_add]
  simp only [smul_eq_mul]
  ring

theorem fourier_normalized_dilation (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (𝓕 (fun ξ : ℝ ↦ ((c : ℂ)⁻¹) * f (ξ / c))) (t / c) = (𝓕 f) t := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  let F : ℝ → ℂ := fun u ↦ Complex.exp (((-2 * Real.pi * u * t : ℝ) : ℂ) * Complex.I) * f u
  have heq : (fun ξ : ℝ ↦ Complex.exp
      (((-2 * Real.pi * ξ * (t / c) : ℝ) : ℂ) * Complex.I) • ((c : ℂ)⁻¹ * f (ξ / c))) =
      (fun ξ : ℝ ↦ (c : ℂ)⁻¹ * F (ξ / c)) := by
    ext ξ
    have hr : -2 * Real.pi * ξ * (t / c) = -2 * Real.pi * (ξ / c) * t := by ring
    simp only [F, hr, smul_eq_mul]
    ring
  rw [heq, integral_const_mul, Measure.integral_comp_div, abs_of_pos hc]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ hcC, one_mul]
  rfl

def selbergFourierFrequencyScale : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 ((2 * Real.pi)⁻¹) (by positivity))

@[simp] theorem selbergFourierFrequencyScale_apply (ξ : ℝ) :
    selbergFourierFrequencyScale ξ = ξ / (2 * Real.pi) := by
  simp [selbergFourierFrequencyScale, div_eq_mul_inv]

def selbergFourierCoefficient (H : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ((2 * Real.pi : ℂ)⁻¹) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ selbergFourierFrequencyScale (𝓕⁻ H)

@[simp] theorem selbergFourierCoefficient_apply (H : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    selbergFourierCoefficient H ξ =
      (2 * Real.pi : ℂ)⁻¹ * (𝓕⁻ H) (ξ / (2 * Real.pi)) := by
  simp [selbergFourierCoefficient, smul_eq_mul]

/-- The precise Fourier inversion normalization used in the source's
Möbius-weight formula. -/
theorem laplaceFourierProfile_selbergFourierCoefficient (H : SchwartzMap ℝ ℂ) (t : ℝ) :
    laplaceFourierProfile (selbergFourierCoefficient H) t =
      Complex.exp (-(t : ℂ)) * H t := by
  rw [laplaceFourierProfile_eq_exp_mul_fourier]
  have hcoeff : (selbergFourierCoefficient H : ℝ → ℂ) =
      fun ξ : ℝ ↦ (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (𝓕⁻ H) (ξ / (2 * Real.pi)) := by
    ext ξ
    simp
  rw [hcoeff]
  have hinv : (𝓕 (fun ξ : ℝ ↦ (𝓕⁻ H) ξ)) t = H t := by
    have h := congrArg (fun u : SchwartzMap ℝ ℂ ↦ u t)
      (fourier_fourierInv_eq (F := SchwartzMap ℝ ℂ) H)
    simpa only [SchwartzMap.fourier_coe] using! h
  congr 1
  calc
    _ = (𝓕 (fun ξ : ℝ ↦ (𝓕⁻ H) ξ)) t := by
      simpa only using! fourier_normalized_dilation (fun ξ : ℝ ↦ (𝓕⁻ H) ξ)
        (by positivity : 0 < 2 * Real.pi) t
    _ = _ := hinv

/-- Every smooth compactly supported profile has the source's Schwartz
frequency representation.  The coefficient is constructed, not assumed. -/
theorem exists_schwartz_laplaceFourierProfile
    (F : ℝ → ℂ) (hcompact : HasCompactSupport F) (hsmooth : ContDiff ℝ ∞ F) :
    ∃ f : SchwartzMap ℝ ℂ, ∀ t : ℝ, laplaceFourierProfile f t = F t := by
  let Hfun : ℝ → ℂ := fun t ↦ Complex.exp (t : ℂ) * F t
  have hHcompact : HasCompactSupport Hfun := hcompact.mul_left
  have hHsmooth : ContDiff ℝ ∞ Hfun := by
    dsimp [Hfun]
    have hcast : ContDiff ℝ ∞ (fun t : ℝ ↦ (t : ℂ)) := Complex.ofRealCLM.contDiff
    exact (Complex.contDiff_exp.comp hcast).mul hsmooth
  let H : SchwartzMap ℝ ℂ := hHcompact.toSchwartzMap hHsmooth
  refine ⟨selbergFourierCoefficient H, fun t ↦ ?_⟩
  rw [laplaceFourierProfile_selbergFourierCoefficient]
  change Complex.exp (-(t : ℂ)) * (Complex.exp (t : ℂ) * F t) = F t
  rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- This is the exact logarithmic-divisor substitution in each Selberg
coefficient.  It is a finite-parameter identity before taking limits. -/
theorem exists_schwartz_selbergProfile_representation
    (F : ℝ → ℂ) (hcompact : HasCompactSupport F) (hsmooth : ContDiff ℝ ∞ F) :
    ∃ f : SchwartzMap ℝ ℂ, ∀ L d : ℝ,
      F (Real.log d / L) =
        ∫ ξ : ℝ, primeFourierPower d (fourierLaplaceParameter ξ / L) * f ξ := by
  obtain ⟨f, hf⟩ := exists_schwartz_laplaceFourierProfile F hcompact hsmooth
  refine ⟨f, fun L d ↦ ?_⟩
  rw [← hf (Real.log d / L)]
  unfold laplaceFourierProfile primeFourierPower
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  congr 1
  push_cast
  ring

theorem exists_schwartz_profile_pair_integral
    (F G : ℝ → ℂ) (hFc : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F)
    (hGc : HasCompactSupport G) (hGs : ContDiff ℝ ∞ G) :
    ∃ f g : SchwartzMap ℝ ℂ,
      (∀ t : ℝ, laplaceFourierProfile f t = F t) ∧
      (∀ t : ℝ, laplaceFourierProfile g t = G t) ∧
      (∫ z : ℝ × ℝ,
        fourierLaplacePairKernel z.1 z.2 * (f z.1 * g z.2) ∂(volume.prod volume)) =
        ∫ t : ℝ in Set.Ioi 0, deriv F t * deriv G t := by
  obtain ⟨f, hf⟩ := exists_schwartz_laplaceFourierProfile F hFc hFs
  obtain ⟨g, hg⟩ := exists_schwartz_laplaceFourierProfile G hGc hGs
  refine ⟨f, g, hf, hg, ?_⟩
  have hfEq : laplaceFourierProfile f = F := funext hf
  have hgEq : laplaceFourierProfile g = G := funext hg
  simpa only [hfEq, hgEq] using integral_fourierLaplacePairKernel_eq_profile_derivatives f g

end

end Erdos4b
