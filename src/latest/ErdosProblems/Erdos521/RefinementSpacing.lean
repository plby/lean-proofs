/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The Gaussian sign-count limit as a fixed logarithmic interval is subdivided.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianSignSlope

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem inverse_nat_spacing_tendsto_right {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun N : ℕ ↦ ℓ / (N : ℝ)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul ℓ)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_pos hℓ (by exact_mod_cast (show 0 < N by omega))

theorem gaussian_grid_refinement_limit {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ) * (gaussianPair (logScaleCorrelation (ℓ / N))).real pairSignFlip)
      atTop (𝓝 (ℓ / (2 * Real.pi))) := by
  have h := (gaussian_log_sign_probability_slope.comp (inverse_nat_spacing_tendsto_right hℓ)).const_mul ℓ
  have hconst : ℓ * (1 / (2 * Real.pi)) = ℓ / (2 * Real.pi) := by ring
  rw [hconst] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  dsimp only [Function.comp_apply]
  have hN₀ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp [hℓ.ne', hN₀]

theorem refinement_exp_ratio_tendsto_one {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Tendsto (fun N : ℕ ↦ (Real.exp (ℓ / N) - 1) / (ℓ / N)) atTop (𝓝 1) := by
  have h : Tendsto (fun t : ℝ ↦ (Real.exp t - 1) / t) (𝓝[>] 0) (𝓝 1) := by
    simpa only [zero_add, Real.exp_zero, smul_eq_mul, div_eq_inv_mul] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  exact h.comp (inverse_nat_spacing_tendsto_right hℓ)

theorem eventually_refinement_exp_le {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᶠ N : ℕ in atTop, Real.exp (ℓ / N) - 1 ≤ (2 * ℓ) / N := by
  filter_upwards [(refinement_exp_ratio_tendsto_one hℓ).eventually
    (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), eventually_ge_atTop 1] with N hN hN₁
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := (div_le_iff₀ (div_pos hℓ hN₀)).mp hN.le
  simpa only [mul_div_assoc] using h

end Erdos521
