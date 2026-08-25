import Util.Bernays.SmoothedFunctional

/-!
# Compactly supported spatial tests and their logarithmic Fourier preimages
-/

open Set Filter Topology MeasureTheory
open scoped FourierTransform ContDiff

namespace Bernays

theorem exists_logarithmic_fourier_test {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : HasCompactSupport Ψ) (hplus : tsupport Ψ ⊆ Ioi 0) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, 0 < y →
      𝓕 (g : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log y) = (y : ℂ) * Ψ y := by
  let h (t : ℝ) : ℂ := (Real.exp (2 * Real.pi * t) : ℂ) * Ψ (Real.exp (2 * Real.pi * t))
  have h₁ : ContDiff ℝ ∞ h := by
    have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (2 * Real.pi * t)) :=
      (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp he).mul (hΨ.comp he)
  have h₂ : HasCompactSupport h := by
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hbase : HasCompactSupport (Ψ ∘ Real.exp) := comp_exp_support hsupp hplus
    have hscaled := hbase.comp_smul (c := (2 * Real.pi : ℝ)) hπ
    have he : HasCompactSupport (fun t : ℝ => Ψ (Real.exp (2 * Real.pi * t))) := by
      simpa only [Function.comp_def, smul_eq_mul] using hscaled
    exact he.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h₁ h₂)
  refine ⟨g, fun y hy => ?_⟩
  rw [← SchwartzMap.fourier_coe, hg]
  change (Real.exp (2 * Real.pi * (1 / (2 * Real.pi) * Real.log y)) : ℂ) *
    Ψ (Real.exp (2 * Real.pi * (1 / (2 * Real.pi) * Real.log y))) = _
  have hid : 2 * Real.pi * (1 / (2 * Real.pi) * Real.log y) = Real.log y := by field_simp
  rw [hid, Real.exp_log hy]

theorem smoothedSeries_eq_spatial_twist {a : ℕ → ℂ} {Ψ : ℝ → ℂ}
    (hplus : tsupport Ψ ⊆ Ioi 0) (g : SchwartzMap ℝ ℂ)
    (hg : ∀ y : ℝ, 0 < y → 𝓕 (g : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log y) = (y : ℂ) * Ψ y)
    (δ : ℝ) :
    smoothedSeries a g δ =
      (∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))) /
        (Real.exp (1 / δ) : ℂ) := by
  rw [smoothedSeries_eq_twist, ← tsum_div_const]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, dirichletTwist]
  · rw [hg _ (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) (Real.exp_pos _))]
    push_cast
    field_simp

theorem spatial_twisted_cancellation_of_smoothed {a : ℕ → ℂ}
    (hsm : ∀ φ : W21,
      Tendsto (fun δ : ℝ => ‖smoothedSeries a φ δ‖ / Real.sqrt δ) (𝓝[>] 0) (𝓝 0))
    {Ψ : ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun δ : ℝ =>
      ‖∑' n : ℕ, dirichletTwist a δ n * Ψ ((n : ℝ) / Real.exp (1 / δ))‖ /
        (Real.exp (1 / δ) * Real.sqrt δ)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨g, hg⟩ := exists_logarithmic_fourier_test hΨ hsupp hplus
  have h := hsm g
  apply h.congr'
  filter_upwards [] with δ
  change ‖smoothedSeries a g δ‖ / Real.sqrt δ = _
  rw [smoothedSeries_eq_spatial_twist hplus g hg, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, div_div]

end Bernays
