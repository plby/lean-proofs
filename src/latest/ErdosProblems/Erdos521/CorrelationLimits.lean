/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The limiting correlation of two normalized Littlewood values.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CovarianceLimits

namespace Erdos521

open Filter
open scoped BigOperators Topology

theorem inverse_scale_sqrt_variance_product {a b : ℝ} (ha : 0 < a) :
    Real.sqrt (1 / (2 * a)) * Real.sqrt (1 / (2 * b)) = 1 / (2 * Real.sqrt (a * b)) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 1 / (2 * a))]
  rw [show (1 / (2 * a)) * (1 / (2 * b)) = 1 / (4 * (a * b)) by ring]
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem normalized_geometricCovariance_tendsto (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop) (hN : Tendsto (fun j ↦ (N j : ℝ) / s j) atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j ↦ geometricCovariance (1 - a / s j) (1 - b / s j) (N j) /
      (Real.sqrt (geometricVariance (1 - a / s j) (N j)) *
        Real.sqrt (geometricVariance (1 - b / s j) (N j)))) atTop
      (𝓝 (2 * Real.sqrt (a * b) / (a + b))) := by
  have hVa := scaled_geometricVariance_tendsto N s hs hN ha
  have hVb := scaled_geometricVariance_tendsto N s hs hN hb
  have hC := scaled_geometricCovariance_tendsto N s hs hN ha hb
  have hden := (Real.continuous_sqrt.continuousAt.tendsto.comp hVa).mul
    (Real.continuous_sqrt.continuousAt.tendsto.comp hVb)
  have hlim := hC.div hden (by positivity :
    Real.sqrt (1 / (2 * a)) * Real.sqrt (1 / (2 * b)) ≠ 0)
  rw [inverse_scale_sqrt_variance_product ha] at hlim
  have hconst : (1 / (a + b)) / (1 / (2 * Real.sqrt (a * b))) =
      2 * Real.sqrt (a * b) / (a + b) := by
    simp only [one_div, div_inv_eq_mul]
    ring
  rw [hconst] at hlim
  apply hlim.congr'
  filter_upwards [hs.eventually_gt_atTop 0] with j hsj
  dsimp only [Pi.div_apply, Function.comp_apply]
  rw [Real.sqrt_div (geometricVariance_nonneg _ _), Real.sqrt_div (geometricVariance_nonneg _ _),
    div_mul_div_comm, ← pow_two, Real.sq_sqrt hsj.le, div_div_div_cancel_right₀ hsj.ne']

theorem normalized_geometric_weight_product_sum (N : ℕ) (x y : ℝ) :
    (∑ i ∈ Finset.range N, (x ^ i / Real.sqrt (geometricVariance x N)) *
      (y ^ i / Real.sqrt (geometricVariance y N))) =
      geometricCovariance x y N / (Real.sqrt (geometricVariance x N) * Real.sqrt (geometricVariance y N)) := by
  simp_rw [div_mul_div_comm, ← mul_pow]
  rw [← Finset.sum_div]
  rfl

theorem normalized_geometric_weight_product_tendsto (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop) (hN : Tendsto (fun j ↦ (N j : ℝ) / s j) atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j ↦ ∑ i ∈ Finset.range (N j),
      ((1 - a / s j) ^ i / Real.sqrt (geometricVariance (1 - a / s j) (N j))) *
        ((1 - b / s j) ^ i / Real.sqrt (geometricVariance (1 - b / s j) (N j)))) atTop
      (𝓝 (2 * Real.sqrt (a * b) / (a + b))) := by
  simp_rw [normalized_geometric_weight_product_sum]
  exact normalized_geometricCovariance_tendsto N s hs hN ha hb

end Erdos521
