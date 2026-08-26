import ErdosProblems.Erdos421.SchwartzWindowScaling
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Poisson expansion of a smoothed divisibility count

The zero Fourier mode is the expected density `1 / m`. The nonzero modes
will be estimated using separation of reduced rational frequencies.
-/

namespace Erdos421

open Complex MeasureTheory FourierTransform
open scoped SchwartzMap

/-- A normalized additive window on the lattice of multiples of `m`. -/
noncomputable def additiveDivisorWindow (φ : 𝓢(ℝ, ℂ)) (Y x : ℝ) (m : ℕ) : ℂ :=
  ∑' n : ℤ, (Y⁻¹ : ℝ) • φ ((x + (m : ℝ) * n) / Y)

theorem additiveDivisorWindow_poisson (φ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) {m : ℕ} (hm : 0 < m) :
    additiveDivisorWindow φ Y x m =
      ∑' h : ℤ, (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
        fourier h ((x / m : ℝ) : UnitAddCircle) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < Y / m := div_pos hY hmR
  have hscale (n : ℤ) :
      (Y⁻¹ : ℝ) • φ ((x + (m : ℝ) * n) / Y) =
        (m : ℂ)⁻¹ * normalizedSchwartzScale (Y / m) hδ φ (x / m + n) := by
    rw [normalizedSchwartzScale_apply]
    have harg : (x / m + (n : ℝ)) / (Y / m) = (x + (m : ℝ) * n) / Y := by
      field_simp
    rw [harg]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_natCast]
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  calc
    _ = (m : ℂ)⁻¹ * ∑' n : ℤ,
        normalizedSchwartzScale (Y / m) hδ φ (x / m + n) := by
      simp only [additiveDivisorWindow, hscale, tsum_mul_left]
    _ = (m : ℂ)⁻¹ * ∑' h : ℤ, 𝓕 φ ((Y / m) * h) *
        fourier h ((x / m : ℝ) : UnitAddCircle) := by
      rw [SchwartzMap.tsum_eq_tsum_fourier]
      simp only [fourier_normalizedSchwartzScale]
    _ = _ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro h
      have harg : (Y / (m : ℝ)) * h = Y * h / m := by ring
      rw [harg, mul_assoc]

theorem summable_schwartz_integer_values (φ : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ ↦ φ (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((φ.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

theorem summable_divisor_fourier_modes (φ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) {m : ℕ} (hm : 0 < m) :
    Summable (fun h : ℤ ↦ (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) *
      fourier h ((x / m : ℝ) : UnitAddCircle)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := summable_schwartz_integer_values
    (𝓕 (normalizedSchwartzScale (Y / m) (div_pos hY hmR) φ))
  simp only [fourier_normalizedSchwartzScale] at hs
  have he : (fun h : ℤ ↦ 𝓕 φ (Y / m * h)) = fun h : ℤ ↦ 𝓕 φ (Y * h / m) := by
    funext h
    congr 1
    ring
  rw [he] at hs
  apply (hs.norm.mul_left ‖(m : ℂ)⁻¹‖).of_norm_bounded
  intro h
  simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one, le_refl]

theorem fourier_schwartz_zero_eq_integral (φ : 𝓢(ℝ, ℂ)) :
    𝓕 φ 0 = ∫ x : ℝ, φ x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp

/-- The main term is removed exactly; all remaining frequencies are nonzero. -/
theorem additiveDivisorWindow_sub_main (φ : 𝓢(ℝ, ℂ)) {Y : ℝ} (hY : 0 < Y)
    (x : ℝ) {m : ℕ} (hm : 0 < m) :
    additiveDivisorWindow φ Y x m - (m : ℂ)⁻¹ * (∫ u : ℝ, φ u) =
      ∑' h : ℤ, if h = 0 then 0 else
        (m : ℂ)⁻¹ * 𝓕 φ (Y * h / m) * fourier h ((x / m : ℝ) : UnitAddCircle) := by
  have hs := summable_divisor_fourier_modes φ hY x hm
  rw [additiveDivisorWindow_poisson φ hY x hm, hs.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, mul_zero, zero_div, fourier_schwartz_zero_eq_integral,
    _root_.fourier_zero, mul_one]
  ring

end Erdos421
