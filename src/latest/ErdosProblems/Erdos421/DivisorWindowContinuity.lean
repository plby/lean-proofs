import ErdosProblems.Erdos421.DivisorWindowFinitePart

/-! # Continuity of the full smoothed divisibility window -/

namespace Erdos421

open FourierTransform
open scoped SchwartzMap

theorem additiveDivisorWindow_continuous (φ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y)
    {m : ℕ} (hm : 0 < m) : Continuous (fun x ↦ additiveDivisorWindow φ Y x m) := by
  have hs := (summable_divisor_fourier_modes φ hY 0 hm).norm
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one] at hs
  have hc : Continuous (fun x : ℝ ↦ ∑' h : ℤ,
      (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) * fourier h ((x / m : ℝ) : UnitAddCircle)) := by
    refine continuous_tsum ?_ hs ?_
    · intro h
      simp only [fourier_divisor_oscillatoryPhase]
      exact continuous_const.mul (oscillatoryPhase_continuous _)
    · intro h x
      simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, le_refl]
  have he : (fun x ↦ additiveDivisorWindow φ Y x m) =
      (fun x : ℝ ↦ ∑' h : ℤ, (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
        fourier h ((x / m : ℝ) : UnitAddCircle)) :=
    funext (fun x ↦ additiveDivisorWindow_poisson φ hY x hm)
  rwa [he]

end Erdos421
