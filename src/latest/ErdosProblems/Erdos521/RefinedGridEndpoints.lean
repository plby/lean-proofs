/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Refinement preserves the endpoints of the logarithmic interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGrid

namespace Erdos521

theorem logGrid_zero (s a δ : ℝ) : logGrid s a δ 0 = 1 - a / s := by
  simp [logGrid, logGridCoefficient]

theorem logGrid_one (s a δ : ℝ) : logGrid s a δ 1 = 1 - (a * Real.exp (-δ)) / s := by
  simp [logGrid, logGridCoefficient]

theorem refined_logGrid_end (s a ℓ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    logGrid s a (ℓ / N) N = logGrid s a ℓ 1 := by
  have hN₀ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : -(N : ℝ) * (ℓ / N) = -ℓ := by field_simp
  rw [logGrid, logGridCoefficient, he, logGrid_one]

theorem short_logGrid_width {s a ℓ : ℝ} (hwidth : Real.exp ℓ - 1 ≤ 1 / 8)
    (hend : logGrid s a ℓ 1 ≤ 1) :
    logGrid s a ℓ 1 - logGrid s a ℓ 0 ≤ (1 - logGrid s a ℓ 1) / 8 := by
  have h := logGrid_span s a ℓ 1
  simp only [Nat.cast_one, one_mul] at h
  rw [h]
  have hbound := mul_le_mul_of_nonneg_right hwidth (sub_nonneg.mpr hend)
  nlinarith

end Erdos521
