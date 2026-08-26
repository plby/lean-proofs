import ErdosProblems.Erdos421.DivisibilityWindows
import ErdosProblems.Erdos421.IntegerFourierTails

/-! # Uniform truncation of the smoothed divisor Poisson series -/

namespace Erdos421

open FourierTransform
open scoped SchwartzMap

theorem divisor_fourier_mode_bound (φ : 𝓢(ℝ, ℂ)) {C : ℝ}
    (hφ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C) {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) {m : ℕ} (hm : 0 < m) {h : ℤ} (hh : h ≠ 0) :
    ‖(m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) * fourier h ((x / m : ℝ) : UnitAddCircle)‖ ≤
      (C * m / Y ^ 2) / (h : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  have ht : 0 < |Y * (h : ℝ) / m| ^ 2 :=
    sq_pos_of_ne_zero (abs_ne_zero.mpr (div_ne_zero (mul_ne_zero hY.ne' hhR) hmR.ne'))
  have hb : ‖𝓕 φ (Y * h / m)‖ ≤ C / |Y * (h : ℝ) / m| ^ 2 :=
    (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hφ (Y * h / m))
  calc
    _ = (m : ℝ)⁻¹ * ‖𝓕 φ (Y * h / m)‖ := by
      simp only [norm_mul, norm_inv, Complex.norm_natCast, fourier_apply, Circle.norm_coe,
        mul_one]
    _ ≤ (m : ℝ)⁻¹ * (C / |Y * (h : ℝ) / m| ^ 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      rw [abs_div, abs_mul, abs_of_pos hY, abs_of_pos hmR, div_pow, mul_pow, sq_abs]
      field_simp

theorem additiveDivisorWindow_truncation_bound (φ : 𝓢(ℝ, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C) {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) {m H : ℕ} (hm : 0 < m) (hH : 0 < H) :
    ‖additiveDivisorWindow φ Y x m -
      ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
        fourier h ((x / m : ℝ) : UnitAddCircle)‖ ≤ 2 * C * m / (Y ^ 2 * H) := by
  let f : ℤ → ℂ := fun h ↦ (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
    fourier h ((x / m : ℝ) : UnitAddCircle)
  let J := Finset.Icc (-(H : ℤ)) (H : ℤ)
  have hf : Summable f := summable_divisor_fourier_modes φ hY x hm
  have hcomp : (↑J : Set ℤ)ᶜ = {n : ℤ | (H : ℤ) < |n|} := by
    ext n
    simp only [J, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, ← abs_le, not_le,
      Set.mem_ofPred_eq]
  rw [additiveDivisorWindow_poisson φ hY x hm]
  change ‖(∑' h : ℤ, f h) - ∑ h ∈ J, f h‖ ≤ _
  rw [← hf.sum_add_tsum_compl (s := J), add_sub_cancel_left, hcomp]
  have hb := integer_tail_series_norm_le f hf (by positivity : 0 ≤ C * (m : ℝ) / Y ^ 2)
    (fun h hh ↦ divisor_fourier_mode_bound φ hφ hY x hm hh) hH
  exact hb.trans_eq (by ring)

end Erdos421
