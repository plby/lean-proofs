/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.Analytic
import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory intervalIntegral

namespace Erdos232

noncomputable section

local instance circleBesselMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance circleBesselIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance circleBesselIsProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The angular definition of `besselJ0` is the normalized Haar average of the real part
of the fundamental character. -/
theorem integral_cos_fourier_one_re (x : ℝ) :
    ∫ θ : UnitAddCircle, Real.cos (x * (fourier 1 θ).re) ∂AddCircle.haarAddCircle =
      besselJ0 x := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) 0]
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := fun θ : ℝ ↦ Real.cos (x * Real.cos θ))
    (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi)
  have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have heval : (∫ t in (0 : ℝ)..1,
      Real.cos (x * ((fourier 1 (t : UnitAddCircle)).re))) =
      ∫ t in (0 : ℝ)..1, Real.cos (x * Real.cos ((2 * Real.pi) * t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    change Real.cos (x * ((fourier 1 (t : UnitAddCircle)).re)) =
      Real.cos (x * Real.cos ((2 * Real.pi) * t))
    rw [fourier_coe_apply]
    simp only [Int.cast_one, mul_one, Complex.exp_re]
    simp [Complex.mul_re, Complex.mul_im]
  simp only [zero_add]
  rw [heval]
  have hscaled : (∫ t in (0 : ℝ)..1, Real.cos (x * Real.cos ((2 * Real.pi) * t))) =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.cos (x * Real.cos θ) := by
    calc
      _ = (2 * Real.pi)⁻¹ * ((2 * Real.pi) *
          ∫ t in (0 : ℝ)..1, Real.cos (x * Real.cos ((2 * Real.pi) * t))) := by
            field_simp
      _ = _ := by
        rw [hscale]
        simp only [mul_zero, mul_one]
  rw [hscaled]
  simp [besselJ0, besselDerivative]

private theorem fourier_one_add (theta phi : UnitAddCircle) :
    fourier 1 (theta + phi) = fourier 1 theta * fourier 1 phi := by
  simp only [fourier_apply, one_zsmul, AddCircle.toCircle_add, Circle.coe_mul]

/-- Rotating an arbitrary complex vector uniformly makes its real projection have the
order-zero Bessel average determined only by the vector norm. -/
theorem integral_cos_fourier_one_mul_re (x : ℝ) (w : ℂ) :
    ∫ theta : UnitAddCircle, Real.cos (x * (fourier 1 theta * w).re)
        ∂AddCircle.haarAddCircle = besselJ0 (x * ‖w‖) := by
  by_cases hw0 : w = 0
  · subst w
    simp [besselJ0_zero]
  · have hrho : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    let v : ℂ := w / (‖w‖ : ℂ)
    have hvnorm : ‖v‖ = 1 := by
      simp [v, norm_div, abs_of_pos hrho, hw0]
    let vcircle : Circle := ⟨v, by simpa [Submonoid.unitSphere] using hvnorm⟩
    let phi : UnitAddCircle := (AddCircle.homeomorphCircle one_ne_zero).symm vcircle
    have hphi : fourier 1 phi = v := by
      rw [fourier_one]
      have hs : (AddCircle.homeomorphCircle one_ne_zero) phi = vcircle := by
        exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply vcircle
      rw [AddCircle.homeomorphCircle_apply] at hs
      simpa [vcircle] using congrArg ((↑) : Circle → ℂ) hs
    have hw : w = (‖w‖ : ℂ) * fourier 1 phi := by
      rw [hphi]
      have hrho0 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hrho.ne'
      unfold v
      symm
      calc
        (‖w‖ : ℂ) * (w / (‖w‖ : ℂ)) =
            (w / (‖w‖ : ℂ)) * (‖w‖ : ℂ) := mul_comm _ _
        _ = w := div_mul_cancel₀ w hrho0
    have hpoint (theta : UnitAddCircle) :
        x * (fourier 1 theta * w).re =
          (x * ‖w‖) * (fourier 1 (theta + phi)).re := by
      calc
        x * (fourier 1 theta * w).re =
            x * (fourier 1 theta * ((‖w‖ : ℂ) * fourier 1 phi)).re := by
          nth_rewrite 1 [hw]
          rfl
        _ = (x * ‖w‖) * (fourier 1 (theta + phi)).re := by
          rw [fourier_one_add]
          simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            zero_mul, add_zero, sub_zero]
          ring
    simp_rw [hpoint]
    rw [integral_add_right_eq_self
      (fun theta : UnitAddCircle ↦ Real.cos ((x * ‖w‖) * (fourier 1 theta).re)) phi]
    exact integral_cos_fourier_one_re (x * ‖w‖)

end

end Erdos232
