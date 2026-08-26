/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Logarithmic grids near the endpoint and their constant pair correlations.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGaussianParameters

namespace Erdos521

noncomputable def logGridCoefficient (a δ : ℝ) (i : ℕ) : ℝ := a * Real.exp (-(i : ℝ) * δ)

noncomputable def logGrid (s a δ : ℝ) (i : ℕ) : ℝ := 1 - logGridCoefficient a δ i / s

theorem logGridCoefficient_pos {a : ℝ} (ha : 0 < a) (δ : ℝ) (i : ℕ) :
    0 < logGridCoefficient a δ i := mul_pos ha (Real.exp_pos _)

theorem logGridCoefficient_ratio (a δ : ℝ) (i k : ℕ) :
    logGridCoefficient a δ i = logGridCoefficient a δ (i + k) * Real.exp ((k : ℝ) * δ) := by
  unfold logGridCoefficient
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem logGrid_mono {s a δ : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hδ : 0 ≤ δ) : Monotone (logGrid s a δ) := by
  intro i j hij
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hcoeff : logGridCoefficient a δ j ≤ logGridCoefficient a δ i := by
    apply mul_le_mul_of_nonneg_left _ ha
    apply Real.exp_le_exp.mpr
    nlinarith
  exact sub_le_sub_left (div_le_div_of_nonneg_right hcoeff hs.le) 1

theorem logGrid_strictMono {s a δ : ℝ} (hs : 0 < s) (ha : 0 < a) (hδ : 0 < δ) :
    StrictMono (logGrid s a δ) := by
  intro i j hij
  have hcast : (i : ℝ) < j := by exact_mod_cast hij
  have hcoeff : logGridCoefficient a δ j < logGridCoefficient a δ i := by
    apply mul_lt_mul_of_pos_left _ ha
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact sub_lt_sub_left (div_lt_div_of_pos_right hcoeff hs) 1

theorem logGrid_width (s a δ : ℝ) (i : ℕ) :
    logGrid s a δ (i + 1) - logGrid s a δ i =
      (Real.exp δ - 1) * (1 - logGrid s a δ (i + 1)) := by
  unfold logGrid
  rw [logGridCoefficient_ratio a δ i 1]
  norm_num
  ring

theorem logGrid_span (s a δ : ℝ) (N : ℕ) :
    logGrid s a δ N - logGrid s a δ 0 =
      (Real.exp ((N : ℝ) * δ) - 1) * (1 - logGrid s a δ N) := by
  unfold logGrid
  rw [logGridCoefficient_ratio a δ 0 N, zero_add]
  ring

theorem normalized_correlation_mul_scale {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * Real.sqrt ((c * a) * (c * b)) / (c * a + c * b) = 2 * Real.sqrt (a * b) / (a + b) := by
  rw [show (c * a) * (c * b) = c ^ 2 * (a * b) by ring, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq hc.le, ← mul_add]
  field_simp

theorem logGrid_correlation {a : ℝ} (ha : 0 < a) (δ : ℝ) (i : ℕ) :
    2 * Real.sqrt (logGridCoefficient a δ i * logGridCoefficient a δ (i + 1)) /
      (logGridCoefficient a δ i + logGridCoefficient a δ (i + 1)) = logScaleCorrelation δ := by
  rw [logGridCoefficient_ratio a δ i 1]
  norm_num
  have h := normalized_correlation_mul_scale (Real.exp_pos δ) zero_lt_one
    (logGridCoefficient_pos ha δ (i + 1))
  simpa only [mul_one, logScaleCorrelation_eq] using h

end Erdos521
