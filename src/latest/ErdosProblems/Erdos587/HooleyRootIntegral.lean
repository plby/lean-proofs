import ErdosProblems.Erdos587.RootWeightGeometry
import ErdosProblems.Erdos587.LocatorWeight

/-! # A fixed positive integral for the root-window plateau -/

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace Erdos587

lemma delta_root_plateau_fourier_zero_lower (f : 𝓢(ℝ, ℂ)) {t U V L C : ℝ}
    (ht : 0 ≤ t) (hU : 0 ≤ U) (hV : 0 ≤ V) (hL : 0 < L) (hC : 0 < C)
    (hUV : U ≤ V) (hupper : t + U + V ≤ L ^ 2) (hspan : L ^ 2 ≤ C * (U + V))
    (hfpos : ∀ x : ℝ, 0 ≤ (f x).re)
    (hfplateau : ∀ z : ℝ, 0 ≤ z → t + V / 8 + 5 * U / 32 ≤ z ^ 2 →
      z ^ 2 ≤ t + V / 2 + 7 * U / 32 → 1 ≤ (f (L⁻¹ * z)).re) :
    1 / (128 * C) ≤ ((𝓕 f : 𝓢(ℝ, ℂ)) 0).re := by
  let a := t + V / 8 + 5 * U / 32
  let b := t + V / 2 + 7 * U / 32
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb : b ≤ L ^ 2 := by dsimp [b]; linarith
  have hsize : L ^ 2 ≤ 2 * C * V := by
    nlinarith [mul_le_mul_of_nonneg_left hUV hC.le]
  have hgap : 2 * (1 / (128 * C)) * L ^ 2 ≤ b - a := by
    have hba : V / 32 ≤ b - a := by dsimp [a, b]; linarith
    have hh : L ^ 2 ≤ (b - a) * (64 * C) := by
      nlinarith [mul_le_mul_of_nonneg_left hba (show 0 ≤ 64 * C by positivity)]
    calc
      _ = L ^ 2 / (64 * C) := by ring
      _ ≤ b - a := (div_le_iff₀ (by positivity : 0 < 64 * C)).mpr hh
  have hroots := sqrt_gap_of_square_gap hL ha hab hb hgap
  let α := Real.sqrt a / L
  let β := Real.sqrt b / L
  have hαβ : α ≤ β := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hab) hL.le
  have hlength : 1 / (128 * C) ≤ β - α := by
    dsimp only [α, β]
    rw [← sub_div, le_div_iff₀ hL]
    linarith
  have hplateau : ∀ x ∈ Set.Icc α β, (1 : ℝ) ≤ (f x).re := by
    intro x hx
    have hlo : Real.sqrt a ≤ L * x := by
      have hh := (div_le_iff₀ hL).mp hx.1
      simpa only [mul_comm] using hh
    have hhi : L * x ≤ Real.sqrt b := by
      have hh := (le_div_iff₀ hL).mp hx.2
      simpa only [mul_comm] using hh
    have hz : 0 ≤ L * x := (Real.sqrt_nonneg a).trans hlo
    have hzlo : a ≤ (L * x) ^ 2 := by
      have hh := pow_le_pow_left₀ (Real.sqrt_nonneg a) hlo 2
      rwa [Real.sq_sqrt ha] at hh
    have hzhi : (L * x) ^ 2 ≤ b := by
      have hh := pow_le_pow_left₀ hz hhi 2
      rwa [Real.sq_sqrt (ha.trans hab)] at hh
    have hh := hfplateau (L * x) hz hzlo hzhi
    simpa only [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] using hh
  have hInt : Integrable (fun x : ℝ => (f x).re) := f.integrable.re
  have hlower := setIntegral_ge_of_const_le_real measurableSet_Icc
    (isCompact_Icc.measure_lt_top.ne) hplateau hInt.integrableOn
  rw [Real.volume_real_Icc_of_le hαβ, one_mul] at hlower
  have hreal := integral_re (𝕜 := ℂ) (μ := volume) f.integrable
  change (∫ x : ℝ, (f x).re) = (∫ x : ℝ, f x).re at hreal
  rw [schwartz_fourier_zero, ← hreal]
  calc
    _ ≤ β - α := hlength
    _ ≤ ∫ x in Set.Icc α β, (f x).re := hlower
    _ ≤ ∫ x : ℝ, (f x).re := setIntegral_le_integral hInt (Filter.Eventually.of_forall hfpos)

lemma delta_fourier_zero_im_eq_zero (f : 𝓢(ℝ, ℂ)) (hf : ∀ x : ℝ, (f x).im = 0) :
    ((𝓕 f : 𝓢(ℝ, ℂ)) 0).im = 0 := by
  have him := integral_im (𝕜 := ℂ) (μ := volume) f.integrable
  change (∫ x : ℝ, (f x).im) = (∫ x : ℝ, f x).im at him
  rw [schwartz_fourier_zero, ← him]
  simp only [hf, integral_zero]

end Erdos587
