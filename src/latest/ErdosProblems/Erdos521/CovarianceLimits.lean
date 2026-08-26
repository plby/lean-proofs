/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Cross-variance asymptotics for pairs of Littlewood evaluations near an endpoint.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ScaleLimits

namespace Erdos521

open Filter
open scoped BigOperators Topology

def geometricCovariance (x y : ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, (x * y) ^ i

theorem geometricCovariance_mul_one_sub_mul (x y : ℝ) (N : ℕ) :
    geometricCovariance x y N * (1 - x * y) = 1 - (x * y) ^ N :=
  geom_sum_mul_neg (x * y) N

theorem inverse_scale_cross_power_tendsto_zero (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop) (hN : Tendsto (fun j ↦ (N j : ℝ) / s j) atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j ↦ ((1 - a / s j) * (1 - b / s j)) ^ N j) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (inverse_scale_power_tendsto_zero N s hs hN ha)
  · filter_upwards [eventually_inverse_scale_point_bounds s hs ha,
      eventually_inverse_scale_point_bounds s hs hb] with j hjx hjy
    exact pow_nonneg (mul_nonneg hjx.1 hjy.1) _
  · filter_upwards [eventually_inverse_scale_point_bounds s hs ha,
      eventually_inverse_scale_point_bounds s hs hb] with j hjx hjy
    exact pow_le_pow_left₀ (mul_nonneg hjx.1 hjy.1)
      (mul_le_of_le_one_right hjx.1 hjy.2.le) _

theorem scaled_geometricCovariance_tendsto (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hs : Tendsto s atTop atTop) (hN : Tendsto (fun j ↦ (N j : ℝ) / s j) atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j ↦ geometricCovariance (1 - a / s j) (1 - b / s j) (N j) / s j)
      atTop (𝓝 (1 / (a + b))) := by
  have hdiv : Tendsto (fun j ↦ a * b / s j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hs).const_mul (a * b)
  have hden : Tendsto (fun j ↦ a + b - a * b / s j) atTop (𝓝 (a + b)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := a + b)).sub hdiv
  have htail := inverse_scale_cross_power_tendsto_zero N s hs hN ha hb
  have hquot : Tendsto (fun j ↦ (1 - ((1 - a / s j) * (1 - b / s j)) ^ N j) /
      (a + b - a * b / s j)) atTop (𝓝 (1 / (a + b))) := by
    convert ((tendsto_const_nhds (x := (1 : ℝ))).sub htail).div hden (by positivity) using 1 <;>
      first | rfl | simp
  have heq : (fun j ↦ (1 - ((1 - a / s j) * (1 - b / s j)) ^ N j) /
      (a + b - a * b / s j)) =ᶠ[atTop]
      (fun j ↦ geometricCovariance (1 - a / s j) (1 - b / s j) (N j) / s j) := by
    filter_upwards [hden.eventually (lt_mem_nhds (add_pos ha hb))] with j hj
    symm
    apply (eq_div_iff hj.ne').mpr
    calc
      (geometricCovariance (1 - a / s j) (1 - b / s j) (N j) / s j) *
          (a + b - a * b / s j) =
          geometricCovariance (1 - a / s j) (1 - b / s j) (N j) *
            (1 - (1 - a / s j) * (1 - b / s j)) := by ring
      _ = _ := geometricCovariance_mul_one_sub_mul _ _ _
  exact hquot.congr' heq

end Erdos521
