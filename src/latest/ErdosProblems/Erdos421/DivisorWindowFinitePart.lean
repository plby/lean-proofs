import ErdosProblems.Erdos421.DivisorWindowTruncation
import ErdosProblems.Erdos421.DirichletMeanValue

/-! # The nonzero finite Fourier part of a divisibility window -/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

theorem fourier_divisor_oscillatoryPhase (h : ℤ) (m : ℕ) (x : ℝ) :
    fourier h ((x / m : ℝ) : UnitAddCircle) =
      oscillatoryPhase (2 * Real.pi * ((h : ℝ) / m)) x := by
  rw [fourier_coe_apply]
  unfold oscillatoryPhase
  congr 1
  push_cast
  ring

noncomputable def divisorWindowFinitePart (φ : 𝓢(ℝ, ℂ)) (Y : ℝ) (H : ℕ)
    (x : ℝ) (m : ℕ) : ℂ :=
  ∑ h ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).erase 0, (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
    fourier h ((x / m : ℝ) : UnitAddCircle)

theorem divisorWindowFinitePart_continuous (φ : 𝓢(ℝ, ℂ)) (Y : ℝ) (H m : ℕ) :
    Continuous (fun x ↦ divisorWindowFinitePart φ Y H x m) := by
  unfold divisorWindowFinitePart
  simp only [fourier_divisor_oscillatoryPhase]
  exact continuous_finsetSum _ (fun h _ ↦ continuous_const.mul (oscillatoryPhase_continuous _))

theorem divisor_window_full_finite_sum (φ : 𝓢(ℝ, ℂ)) (Y x : ℝ) (H m : ℕ) :
    (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
      fourier h ((x / m : ℝ) : UnitAddCircle)) =
      (m : ℂ)⁻¹ * (∫ u : ℝ, φ u) + divisorWindowFinitePart φ Y H x m := by
  have h0 : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.add_sum_erase _ _ h0]
  simp only [Int.cast_zero, mul_zero, zero_div, fourier_schwartz_zero_eq_integral,
    _root_.fourier_zero, mul_one, divisorWindowFinitePart]

theorem divisorWindowFinitePart_error (φ : 𝓢(ℝ, ℂ)) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ t : ℝ, |t| ^ 2 * ‖𝓕 φ t‖ ≤ C) {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) {m H : ℕ} (hm : 0 < m) (hH : 0 < H) :
    ‖(additiveDivisorWindow φ Y x m - (m : ℂ)⁻¹ * (∫ u : ℝ, φ u)) -
      divisorWindowFinitePart φ Y H x m‖ ≤ 2 * C * m / (Y ^ 2 * H) := by
  have hb := additiveDivisorWindow_truncation_bound φ hC hφ hY x hm hH
  rw [divisor_window_full_finite_sum] at hb
  simpa only [sub_sub] using hb

end Erdos421
