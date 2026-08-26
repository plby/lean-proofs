/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A central limit theorem for finite triangular arrays of fair-sign coefficients.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.TriangularComparison
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

theorem triangular_weights_mul_small (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |a n i| < r) (t : ℝ) :
    ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |t * a n i| < r := by
  intro r hr
  have ht : 0 < |t| + 1 := by positivity
  filter_upwards [hsmall (r / (|t| + 1)) (div_pos hr ht)] with n hn
  intro i hi
  rw [abs_mul]
  calc
    |t| * |a n i| ≤ (|t| + 1) * |a n i| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (|t| + 1) * (r / (|t| + 1)) := mul_lt_mul_of_pos_left (hn i hi) ht
    _ = r := by field_simp

theorem triangular_linearForm_charFun_tendsto (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    {V : ℝ} (hV : 0 ≤ V)
    (hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |a n i| < r)
    (hvariance : Tendsto (fun n ↦ ∑ i ∈ s n, (a n i) ^ 2) atTop (𝓝 V)) (t : ℝ) :
    Tendsto (fun n ↦ charFun (sequenceLaw.map (fun ε ↦ ∑ i ∈ s n, a n i * ε i)) t) atTop
      (𝓝 (Real.exp (-V * t ^ 2 / 2) : ℂ)) := by
  have hvar : Tendsto (fun n ↦ ∑ i ∈ s n, (t * a n i) ^ 2) atTop (𝓝 (t ^ 2 * V)) := by
    simp_rw [mul_pow, ← Finset.mul_sum]
    exact hvariance.const_mul (t ^ 2)
  have h := triangular_cosine_products_tendsto s (fun n i ↦ t * a n i)
    (mul_nonneg (sq_nonneg t) hV) (triangular_weights_mul_small s a hsmall t) hvar
  rw [show -(t ^ 2 * V) / 2 = -V * t ^ 2 / 2 by ring] at h
  simpa only [charFun_linearForm] using h

theorem triangular_sign_central_limit (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ) (v : ℝ≥0)
    (hsmall : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ s n, |a n i| < r)
    (hvariance : Tendsto (fun n ↦ ∑ i ∈ s n, (a n i) ^ 2) atTop (𝓝 (v : ℝ))) :
    TendstoInDistribution (fun n ε ↦ ∑ i ∈ s n, a n i * ε i) atTop (fun x : ℝ ↦ x)
      (fun _ ↦ sequenceLaw) (gaussianReal 0 v) where
  forall_aemeasurable n :=
    (Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_pi_apply i)).aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    change Tendsto (fun n ↦ charFun (sequenceLaw.map (fun ε ↦ ∑ i ∈ s n, a n i * ε i)) t)
      atTop (𝓝 (charFun ((gaussianReal 0 v).map (fun x : ℝ ↦ x)) t))
    rw [Measure.map_id', charFun_gaussianReal]
    have h := triangular_linearForm_charFun_tendsto s a v.coe_nonneg hsmall hvariance t
    convert h using 1
    simp [Complex.ofReal_exp, neg_div]

end Erdos521
