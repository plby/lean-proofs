import ErdosProblems.Erdos587.HooleyPeriodicDensity
import ErdosProblems.Erdos587.HooleyRootIntegral

/-! # The power-separated main term with one log-log loss -/

open scoped SchwartzMap FourierTransform

namespace Erdos587

lemma deltaPeriodicSquareMain_re (f g : 𝓢(ℝ, ℂ)) (a q t : ℕ) (L σ : ℝ)
    (hf : ∀ x : ℝ, (f x).im = 0) :
    (deltaPeriodicSquareMain f g a q t L σ).re =
      L * ((𝓕 f : 𝓢(ℝ, ℂ)) 0).re * (deltaPeriodicSquareDensity g a q t σ).re := by
  simp only [deltaPeriodicSquareMain, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, delta_fourier_zero_im_eq_zero f hf, zero_mul, mul_zero, sub_zero, zero_add]

theorem exists_delta_periodic_main_plateau (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (f g : 𝓢(ℝ, ℂ)) (a u b q H J t X : ℕ) (L : ℝ), 0 < q →
      a * u = b * q + 1 → u.Coprime q → q ≤ X → A * Real.sqrt q ≤ H → 0 < L →
      (u : ℝ) * H ≤ q * J → (t : ℝ) + u * H + q * J ≤ L ^ 2 →
      L ^ 2 ≤ C₀ * ((u : ℝ) * H + q * J) →
      (∀ x : ℝ, (f x).im = 0) → (∀ x : ℝ, 0 ≤ (f x).re) →
      (∀ x : ℝ, 0 ≤ (g x).re) →
      (∀ z : ℝ, 0 ≤ z → (t : ℝ) + q * J / 8 + 5 * ((u : ℝ) * H) / 32 ≤ z ^ 2 →
        z ^ 2 ≤ t + (q : ℝ) * J / 2 + 7 * ((u : ℝ) * H) / 32 → 1 ≤ (f (L⁻¹ * z)).re) →
      (∀ x ∈ Set.Icc (5 / 32 : ℝ) (7 / 32), 1 ≤ (g x).re) →
      L * H / (C * q * max 1 (Real.log (Real.log (X : ℝ)))) ≤
        (deltaPeriodicSquareMain f g a q t L (((q : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, D, hD, hdensity⟩ := exists_delta_periodic_density_plateau_bound
  refine ⟨A, hA, 128 * C₀ * D, by positivity, ?_⟩
  intro f g a u b q H J t X L hq hab hu hqX hscale hL horient hupper hspan
    hf hfpos hgpos hfplateau hgplateau
  have hroot := delta_root_plateau_fourier_zero_lower f (Nat.cast_nonneg t)
    (show (0 : ℝ) ≤ u * H by positivity) (show (0 : ℝ) ≤ q * J by positivity)
    hL hC₀ horient hupper hspan hfpos hfplateau
  have hden := hdensity g a u b q H t X hq hab hu hqX hscale hgpos hgplateau
  have hf0 : 0 ≤ ((𝓕 f : 𝓢(ℝ, ℂ)) 0).re := (by positivity : (0 : ℝ) ≤ 1 / (128 * C₀)).trans hroot
  rw [deltaPeriodicSquareMain_re f g a q t L _ hf]
  calc
    _ = L * ((1 / (128 * C₀)) *
        ((H : ℝ) / (D * q * max 1 (Real.log (Real.log (X : ℝ)))))) := by ring
    _ ≤ L * (((𝓕 f : 𝓢(ℝ, ℂ)) 0).re *
        (deltaPeriodicSquareDensity g a q t (((q : ℝ) / H)⁻¹)).re) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hroot hden (by positivity) hf0) hL.le
    _ = _ := by ring

end Erdos587
