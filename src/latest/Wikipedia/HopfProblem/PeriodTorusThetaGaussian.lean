import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian decay forces an entire function to vanish

A negative Gaussian bound is globally bounded, so Liouville's theorem makes
the entire function constant. Along the real axis the bound tends to zero,
and hence that constant is zero.
-/

namespace Wikipedia.HopfProblem.PeriodTorusTheta

open Filter
open scoped Topology

theorem gaussian_decay_entire_eq_zero (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C a : ℝ) (hC : 0 ≤ C) (ha : a < 0)
    (hb : ∀ t, ‖g t‖ ≤ C * Real.exp (a * ‖t‖ ^ 2)) : ∀ t, g t = 0 := by
  have hBoundNorm (t : ℂ) : ‖g t‖ ≤ C := by
    calc
      ‖g t‖ ≤ C * Real.exp (a * ‖t‖ ^ 2) := hb t
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg ‖t‖))) hC
      _ = C := mul_one C
  have hBound : Bornology.IsBounded (Set.range g) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hBoundNorm t
  have hConst (t : ℂ) : g t = g 0 := hg.apply_eq_apply_of_bounded hBound t 0
  have hPow : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hDecay : Tendsto (fun r : ℝ => C * Real.exp (a * r ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (Real.tendsto_exp_atBot.comp (hPow.const_mul_atTop_of_neg ha)).const_mul C
  have hConstBound (r : ℝ) : ‖g 0‖ ≤ C * Real.exp (a * r ^ 2) := by
    have h := hb (r : ℂ)
    rw [hConst] at h
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  have hZero : g 0 = 0 := norm_le_zero_iff.mp (ge_of_tendsto' hDecay hConstBound)
  intro t
  exact (hConst t).trans hZero

theorem gaussian_decay_entire_zero (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C a : ℝ) (hC : 0 ≤ C) (ha : a < 0)
    (hb : ∀ t, ‖g t‖ ≤ C * Real.exp (a * ‖t‖ ^ 2)) : g 0 = 0 :=
  gaussian_decay_entire_eq_zero g hg C a hC ha hb 0

end Wikipedia.HopfProblem.PeriodTorusTheta
