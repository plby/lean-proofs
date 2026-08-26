import ErdosProblems.Erdos421.PrimeCofactorTwoWindows

/-! # Coefficient scaling and real-part contraction for product-window energy -/

namespace Erdos421

open MeasureTheory
open scoped SchwartzMap

theorem scaledProductWindow_const_mul (S T : Finset ℕ) (a b : ℕ → ℂ) (c : ℂ)
    (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) (δ y : ℝ) :
    scaledProductWindow S T (fun n ↦ c * a n) b σ φ δ y =
      c * scaledProductWindow S T a b σ φ δ y := by
  unfold scaledProductWindow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem scaledProductWindow_energy_integrable (S T : Finset ℕ) (a b : ℕ → ℂ)
    (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    Integrable (fun y : ℝ ↦ ‖scaledProductWindow S T a b σ φ δ y -
      scaledProductWindow S T a b σ φ ρ y‖ ^ 2) := by
  have hi := ((schwartzProductWindow S T a b σ (normalizedSchwartzScale δ hδ φ) -
    schwartzProductWindow S T a b σ (normalizedSchwartzScale ρ hρ φ)).memLp 2).integrable_norm_pow
      (by decide : 2 ≠ 0)
  simpa only [sub_apply, schwartzProductWindow_normalized_apply] using hi

theorem scaledProductWindow_real_energy_le (S T : Finset ℕ) (a b : ℕ → ℂ)
    (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (∫ y : ℝ, |(scaledProductWindow S T a b σ φ δ y).re -
      (scaledProductWindow S T a b σ φ ρ y).re| ^ 2) ≤
        ∫ y : ℝ, ‖scaledProductWindow S T a b σ φ δ y -
          scaledProductWindow S T a b σ φ ρ y‖ ^ 2 := by
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y ↦ sq_nonneg _))
    (scaledProductWindow_energy_integrable S T a b σ φ hδ hρ)
  filter_upwards [] with y
  rw [← Complex.sub_re]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

end Erdos421
