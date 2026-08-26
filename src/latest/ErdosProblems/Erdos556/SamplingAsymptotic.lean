import ErdosProblems.Erdos556.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The asymptotic sampling inequality

The number of endpoint pairs is quadratic, while independent trial failure
decays geometrically in a linear number of trials. This file proves the
needed eventual inequality, including the integer division in that count.
-/

namespace Erdos556

open Filter
open scoped Topology

theorem tendsto_sq_add_one_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r ^ n) atTop (𝓝 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
  have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  convert (h2.add (h1.const_mul 2)).add h0 using 1
  · ext n
    ring
  · norm_num

theorem tendsto_sq_mul_pow_div (K : ℕ) (hK : 0 < K) (C : ℝ) (hC : 0 ≤ C)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * C * r ^ (n / K)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => n / K) atTop atTop :=
    Nat.tendsto_div_const_atTop hK.ne'
  have hmajor : Tendsto
      (fun n : ℕ => ((K : ℝ) ^ 2 * C) * (((n / K : ℕ) : ℝ) + 1) ^ 2 * r ^ (n / K))
      atTop (𝓝 0) := by
    convert ((tendsto_sq_add_one_mul_pow hr0 hr1).comp hdiv).const_mul
      ((K : ℝ) ^ 2 * C) using 1
    · ext n
      simp only [Function.comp_apply]
      ring
    · simp
  apply squeeze_zero (fun n => by positivity) (fun n => ?_) hmajor
  have hn : n ≤ K * (n / K + 1) := by
    have hmod := Nat.mod_lt n hK
    have hdecomp := Nat.mod_add_div n K
    nlinarith
  have hnR : (n : ℝ) ≤ (K : ℝ) * (((n / K : ℕ) : ℝ) + 1) := by
    exact_mod_cast hn
  have hsq : (n : ℝ) ^ 2 ≤ ((K : ℝ) * (((n / K : ℕ) : ℝ) + 1)) ^ 2 := by
    gcongr
  calc
    (n : ℝ) ^ 2 * C * r ^ (n / K) ≤
        ((K : ℝ) * (((n / K : ℕ) : ℝ) + 1)) ^ 2 * C * r ^ (n / K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hC) (pow_nonneg hr0 _)
    _ = ((K : ℝ) ^ 2 * C) * (((n / K : ℕ) : ℝ) + 1) ^ 2 * r ^ (n / K) := by ring

theorem eventually_reservoir_failure (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (L K a : ℕ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 * (a + 1) * (1 - q ^ L) ^ (n / K) < 1 / 2 := by
  have hr0 : 0 ≤ 1 - q ^ L := sub_nonneg.mpr (pow_le_one₀ hq0.le hq1)
  have hr1 : 1 - q ^ L < 1 := by have := pow_pos hq0 L; linarith
  have h := tendsto_sq_mul_pow_div K hK ((a : ℝ) + 1) (by positivity) hr0 hr1
  exact h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

#print axioms eventually_reservoir_failure

end Erdos556
