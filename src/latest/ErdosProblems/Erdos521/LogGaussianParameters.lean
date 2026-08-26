/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Correlation and noise parameters at logarithmically spaced points.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPair

namespace Erdos521

noncomputable def logScaleCorrelation (δ : ℝ) : ℝ :=
  2 * Real.exp (δ / 2) / (Real.exp δ + 1)

noncomputable def logScaleNoise (δ : ℝ) : ℝ :=
  (Real.exp δ - 1) / (2 * Real.exp (δ / 2))

theorem logScaleCorrelation_pos (δ : ℝ) : 0 < logScaleCorrelation δ := by
  unfold logScaleCorrelation
  positivity

theorem logScaleCorrelation_eq (δ : ℝ) :
    logScaleCorrelation δ = 2 * Real.sqrt (Real.exp δ * 1) / (Real.exp δ + 1) := by
  rw [mul_one, ← Real.exp_half]
  rfl

theorem logScaleCorrelation_sq_le_one (δ : ℝ) : logScaleCorrelation δ ^ 2 ≤ 1 := by
  rw [logScaleCorrelation_eq]
  exact inverse_scale_correlation_sq_le_one (Real.exp_pos _) zero_lt_one

theorem logScaleNoise_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ logScaleNoise δ :=
  div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hδ)) (by positivity)

theorem logScaleNoise_pos {δ : ℝ} (hδ : 0 < δ) : 0 < logScaleNoise δ :=
  div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hδ)) (by positivity)

theorem logScaleNoise_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.sqrt (1 - logScaleCorrelation δ ^ 2) / logScaleCorrelation δ = logScaleNoise δ := by
  have hρ := logScaleCorrelation_pos δ
  apply (div_eq_iff hρ.ne').mpr
  apply (Real.sqrt_eq_iff_eq_sq (sub_nonneg.mpr (logScaleCorrelation_sq_le_one δ))
    (mul_nonneg (logScaleNoise_nonneg hδ) hρ.le)).mpr
  have he : Real.exp δ = Real.exp (δ / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add, add_halves]
  unfold logScaleCorrelation logScaleNoise
  rw [he]
  field_simp
  ring

end Erdos521
