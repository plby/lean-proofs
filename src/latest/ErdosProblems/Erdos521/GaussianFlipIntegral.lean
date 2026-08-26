/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The correlated Gaussian sign-change probability as an averaged small interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianLinearMaps
import ErdosProblems.Erdos521.GaussianProduct
import ErdosProblems.Erdos521.GaussianSignSections

namespace Erdos521

open MeasureTheory ProbabilityTheory

theorem gaussianPair_signFlip_eq_product {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ ^ 2 ≤ 1) :
    gaussianPair ρ pairSignFlip = ((gaussianReal 0 1).prod (gaussianReal 0 1))
      {p : ℝ × ℝ | p.1 * (p.1 + (Real.sqrt (1 - ρ ^ 2) / ρ) * p.2) < 0} := by
  rw [gaussianPair_signFlip_eq_standard hρ,
    ← standardGaussian_pair_coordinates.measure_preimage (by
      exact (measurableSet_lt (by fun_prop) measurable_const).nullMeasurableSet)]
  congr 1
  ext x
  change x 0 * (ρ * x 0 + Real.sqrt (1 - ρ ^ 2) * x 1) < 0 ↔
    x 0 * (x 0 + (Real.sqrt (1 - ρ ^ 2) / ρ) * x 1) < 0
  have heq : x 0 * (ρ * x 0 + Real.sqrt (1 - ρ ^ 2) * x 1) =
      ρ * (x 0 * (x 0 + (Real.sqrt (1 - ρ ^ 2) / ρ) * x 1)) := by
    field_simp [hρ₀.ne']
  rw [heq]
  simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hρ₀ :
    ρ * (x 0 * (x 0 + (Real.sqrt (1 - ρ ^ 2) / ρ) * x 1)) < ρ * 0 ↔
      x 0 * (x 0 + (Real.sqrt (1 - ρ ^ 2) / ρ) * x 1) < 0)

theorem gaussianPair_signFlip_integral {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ ^ 2 ≤ 1) :
    (gaussianPair ρ).real pairSignFlip =
      ∫ y : ℝ, standardGaussianInterval ((Real.sqrt (1 - ρ ^ 2) / ρ) * |y|) ∂gaussianReal 0 1 := by
  rw [measureReal_def, gaussianPair_signFlip_eq_product hρ₀ hρ, ← measureReal_def,
    measureReal_prod_sections _ _ (measurableSet_lt (by fun_prop) measurable_const)]
  apply integral_congr_ae
  filter_upwards [] with y
  exact standardGaussian_sign_section (div_nonneg (Real.sqrt_nonneg _) hρ₀.le) y

end Erdos521
